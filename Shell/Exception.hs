-----------------------------------------------------------------------------
-- |
-- Module      :  System.Console.Shell.Exception
-- Copyright   :  (c) The University of Glasgow 2001
--                (c) Brian Hulley 2006
-- License     :  BSD-style (see the file libraries/base/LICENSE)
-- 
-- Maintainer  :  -- not in the library at the moment!
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module provides support for raising and catching both built-in
-- and user-defined exceptions in user defined monads. It is adapted from
-- Control.Exception and extends the code supplied by oleg at pobox.com on the
-- Haskell mailing list to lift all functions in Control.Exception to all
-- monads formed by applying common monad transformers to monads based on IO.
--
-- Refs: <http://www.haskell.org/pipermail/haskell/2006-February/017547.html>
--
-- To use this you should hide all the conflicting Prelude functions or
-- disable implicit Prelude and use a minimal Prelude as suggested in
-- <http://hackage.haskell.org/trac/haskell-prime/wiki/Prelude>
--
-- THIS MODULE HAS NOT BEEN FULLY TESTED AND IS JUST PROVIDED AS AN
-- EXAMPLE FOR DISCUSSION. In particular, you should read Oleg's comments above
-- regarding semantics of the different monads under exceptions, and if in
-- doubt, consider ReaderT instead of StateT.
--
-- If you find any bugs in this module, please add a note to the Haskell' ticket
-- or send an email to brianh at metamilk.com
-----------------------------------------------------------------------------

module Shell.Exception
    ( MonadException(..)
    
    , C.Exception(..)
    , C.IOException
    , C.ArithException(..)
    , C.ArrayException(..)
    , C.AsyncException(..)

    , C.mapException
    , C.ioErrors
    , C.arithExceptions
    , C.errorCalls
    , C.dynExceptions
    , C.assertions
    , C.asyncExceptions
    , C.userErrors

    , C.assert

    , ioError
    , evaluate
    , getUncaughtExceptionHandler

    , C.throw
    , C.throwDyn

    , throwM
    , throwTo
    , throwDynTo

    , handle
    , handleDyn
    , handleJust
    , catchDyn
    , catchJust
    , try
    , tryJust
    , bracket
    , bracket_
    , finally

    ) where

import Prelude hiding (ioError, catch)
import qualified Control.Exception as C
import Control.Monad.RWS
import Control.Monad.Error
import Control.Monad.List
import Control.Concurrent (ThreadId)
import Data.Monoid
import Data.Dynamic

type Exception = C.Exception

ioError :: MonadIO m => IOError -> m a
ioError i = liftIO $ C.ioError i

evaluate :: MonadIO m => a -> m a
evaluate a = liftIO $ C.evaluate a

getUncaughtExceptionHandler :: MonadIO m => m (Exception -> m ())
getUncaughtExceptionHandler = do
            e_io <- liftIO $ C.getUncaughtExceptionHandler
            return $ \e -> liftIO (e_io e)

throwM :: MonadIO m => Exception -> m a
throwM e = liftIO $ C.throwIO e

throwTo :: MonadIO m => ThreadId -> Exception -> m ()
throwTo t e = liftIO $ C.throwTo t e

throwDynTo :: (MonadIO m, Typeable exception) => ThreadId -> exception -> m ()
throwDynTo t e = liftIO $ C.throwDynTo t e

-- | It is debatable whether or not @MonadException@ should derive from @MonadIO@ since
-- none of the functions require @MonadIO@. However a @MonadException@ context will
-- usually also involve use of @liftIO@ or @throwM@ etc which needs a @MonadIO@

class MonadIO m => MonadException m where
    catch :: m a -> (Exception -> m a) -> m a

    block, unblock :: m a -> m a

    -- It is debatable whether or not this very low level function should be
    -- part of the class at all or should just remain tied to the IO monad
    setUncaughtExceptionHandler :: (Exception -> m ()) -> m ()


instance MonadException IO where
    catch = C.catch
    block = C.block
    unblock = C.unblock
    setUncaughtExceptionHandler = C.setUncaughtExceptionHandler

-- In the code that follows, om is used to mean "outer monad" so that it is
-- clearly distinguished from m which is the type of the inner monad
-- Also, "e_om" represents the handler so that it's easy to see that "e_om e" = an outer monad

instance MonadException m => MonadException (StateT s m) where
    catch om e_om = StateT $ \s -> catch (runStateT om s) (\e -> runStateT (e_om e) s)

    block om = StateT $ \s -> block (runStateT om s)
    unblock om = StateT $ \s -> unblock (runStateT om s)    

    setUncaughtExceptionHandler e_om = StateT $ \s -> do
                                                        setUncaughtExceptionHandler $ \e -> do
                                                                runStateT (e_om e) s
                                                                return ()
                                                        return ((), s)


instance MonadException m => MonadException (ReaderT r m) where
    catch om e_om = ReaderT $ \r -> catch (runReaderT om r) (\e -> runReaderT (e_om e) r)

    block om = ReaderT $ \r -> block (runReaderT om r)
    unblock om = ReaderT $ \r -> unblock (runReaderT om r)

    setUncaughtExceptionHandler e_om = ReaderT $ \r ->
                                            setUncaughtExceptionHandler (\e -> runReaderT (e_om e) r)


instance (MonadException m, Monoid w) => MonadException (WriterT w m) where
    catch om e_om = WriterT $ catch (runWriterT om) (\e -> runWriterT (e_om e))

    block om = WriterT $ block (runWriterT om)
    unblock om = WriterT $ unblock (runWriterT om)

    setUncaughtExceptionHandler e_om = do
                                (_,w) <- listen (return ())
                                WriterT $ do
                                            setUncaughtExceptionHandler (\e -> do
                                                runWriterT (e_om e)
                                                return ())
                                            return ((), w)

                                
instance (MonadException m, Monoid w) => MonadException (RWST r w s m) where
    catch om e_om = RWST $ \r s -> catch (runRWST om r s) (\e -> runRWST (e_om e) r s)

    block om = RWST $ \r s -> block (runRWST om r s)
    unblock om = RWST $ \r s -> unblock (runRWST om r s)

    setUncaughtExceptionHandler e_om = do
                                (_,w) <- listen (return ())
                                RWST $ \r s -> do
                                            setUncaughtExceptionHandler (\e -> do
                                                runRWST (e_om e) r s
                                                return ())
                                            return ((),s,w)


instance (MonadException m, Error e) => MonadException (ErrorT e m) where
    catch om e_om = ErrorT $ catch (runErrorT om) (\e -> runErrorT (e_om e))
    
    block om = ErrorT $ block (runErrorT om)
    unblock om = ErrorT $ unblock (runErrorT om)

    setUncaughtExceptionHandler e_om = ErrorT $ do
                                                    setUncaughtExceptionHandler (\e -> do
                                                        runErrorT (e_om e)
                                                        return ())
                                                    return (Right ())


instance MonadException m => MonadException (ListT m) where
    catch om e_om = ListT $ catch (runListT om) (\e -> runListT (e_om e))

    block om = ListT $ block (runListT om)
    unblock om = ListT $ unblock (runListT om)

    setUncaughtExceptionHandler e_om = ListT $ do
                                                    setUncaughtExceptionHandler (\e -> do
                                                        runListT (e_om e)
                                                        return ())
                                                    return [()]
                                    

-- The following are pasted from Control.Exception with IO replaced by an instance of MonadException

catchDyn :: (Typeable exception, MonadException m) => m a -> (exception -> m a) -> m a
catchDyn m k = catch m nwhandle
    where nwhandle ex = case ex of
                          (C.DynException dyn) ->
                             case fromDynamic dyn of
                                Just exception  -> k exception
                                Nothing -> C.throw ex
                          _ -> C.throw ex


handle :: MonadException m => (Exception -> m a) -> m a -> m a
handle x y = catch y x

handleDyn :: (Typeable exception, MonadException m) => (exception -> m a) -> m a -> m a
handleDyn x y = catchDyn y x
    
handleJust :: MonadException m => (Exception -> Maybe b) -> (b -> m a) -> m a -> m a
handleJust x y z = catchJust x z y

bracket :: MonadException m => m a -> (a -> m b) -> (a -> m c) -> m c
bracket before after thing =
  block $ do
    a <- before 
    r <- catch 
              (unblock (thing a))
              (\e -> do { after a; C.throw e })
    after a
    return r

bracket_ :: MonadException m => m a -> m b -> m c -> m c
bracket_ before after thing = bracket before (const after) (const thing)

finally :: MonadException m => m a -> m b -> m a
finally a sequel =
    block $ do
        r <- catch 
                 (unblock a)
                 (\e -> do { sequel; C.throw e })
        sequel
        return r

catchJust :: MonadException m => (Exception -> Maybe b) -> m a -> (b -> m a) -> m a
catchJust p a handler = catch a handler'
  where handler' e = case p e of 
                        Nothing -> C.throw e
                        Just b  -> handler b

try :: MonadException m => m a -> m (Either Exception a)
try a = catch (a >>= \ v -> return (Right v)) (\e -> return (Left e))

tryJust :: MonadException m => (Exception -> Maybe b) -> m a -> m (Either b a)
tryJust p a = do
  r <- try a
  case r of
    Right v -> return (Right v)
    Left  e -> case p e of
                    Nothing -> C.throw e
                    Just b  -> return (Left b)
