module Language.Haskell.THSyntax 
-- FIXME: *urgh* we don't really want to export stuff like `counter'  -=chak
where

import Monad            ( liftM, sequence )

import Data.IORef       ( IORef, newIORef, readIORef, writeIORef )
import System.IO.Unsafe ( unsafePerformIO )
import Text.PrettyPrint.HughesPJ
import Char (toLower)


-------------------------------------------------------
-- The quotation monad as IO

newtype Q a = Q (IO a)
unQ (Q a)   = a

instance Monad Q where
   return x    = Q (return x)
   (Q m) >>= k = Q (m >>= \r -> unQ (k r))
   fail s      = Q (fail s)
   
qIO :: IO a -> Q a
qIO io = Q io

runQ :: Q a -> IO a
runQ (Q io) = io

-- FIXME: What is the point of `returnQ', `bindQ, and `sequenceQ'?  As long as
--   Q is an instance of Monad, we get all this for free.  -=chak
--   Note: if this is to have these functions available in DsMeta, I think,
--   they should be moved to a different module (ie, separate the user-level
--   interface to THSyntax from the GHC-internal one)
--
returnQ :: a -> Q a
returnQ = return

bindQ :: Q a -> (a -> Q b) -> Q b
bindQ = (>>=)

sequenceQ :: [Q a] -> Q [a]
sequenceQ = sequence

-- global variable to generate unique symbols
--
counter :: IORef Int
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)

gensym :: String -> Q String
gensym s = Q( do { n <- readIORef counter
                 ; writeIORef counter (n+1)
                 ; return(s++"'"++(show n)) })

class Lift t where
  lift :: t -> Expr
  
instance Lift Integer where
  lift = return . Lit . Integer

instance Lift Char where
  lift = return . Lit . Char

instance Lift a => Lift [a] where
  lift xs = listExp (map lift xs)

-- TH has a special form for literal strings,
-- which we should take advantage of
{-# RULES "TH:liftString" forall s. lift s = return (Lit (String s)) #-}



------------------------------------------------------

data Lit = Integer Integer 
	 | Char Char 
	 | String String 
	 | Rational Rational 
	 deriving( Show )

data Pat 
  = Plit Lit                      -- { 5 or 'c' }
  | Pvar String                   -- { x }
  | Ptup [Pat]                    -- { (p1,p2) }
  | Pcon String [Pat]             -- data T1 = C1 t1 t2; {C1 p1 p1} = e 
  | Ptilde Pat                    -- { ~p }
  | Paspat String Pat             -- { x @ p }
  | Pwild                         -- { _ }
  deriving( Show )


data Match p e d  = Mat p (RightHandSide e) [d]
                                    -- case e of { pat -> body where decs } 
    deriving Show
data Clause p e d = Clause [p] (RightHandSide e) [d]
                                    -- f { p1 p2 = body where decs }
    deriving Show
 
data Exp 
  = Var String                           -- { x }
  | Con String                           -- data T1 = C1 t1 t2; p = {C1} e1 e2  
  | Lit Lit                              -- { 5 or 'c'}
  | App Exp Exp                          -- { f x }

  | Infix (Maybe Exp) Exp (Maybe Exp)    -- {x + y} or {(x+)} or {(+ x)} or {(+)}
	-- It's a bit gruesome to use an Exp as the
	-- operator, but how else can we distinguish
	-- constructors from non-constructors?
	-- Maybe there should be a var-or-con type?
	-- Or maybe we should leave it to the String itself?

  | Lam [Pat] Exp                        -- { \ p1 p2 -> e }
  | Tup [Exp]                            -- { (e1,e2) }  
  | Cond Exp Exp Exp                     -- { if e1 then e2 else e3 }
  | Let [Dec] Exp                        -- { let x=e1;   y=e2 in e3 }
  | Case Exp [Match Pat Exp Dec]         -- { case e of m1; m2 }
  | Do [Statement Pat Exp Dec]           -- { do { p <- e1; e2 }  }
  | Comp [Statement Pat Exp Dec]         -- { [ (x,y) | x <- xs, y <- ys ] }
  | ArithSeq (DotDot Exp)                -- { [ 1 ,2 .. 10 ] }
  | ListExp [ Exp ]                      -- { [1,2,3] }
  | SigExp Exp Typ			 -- e :: t
  deriving( Show )

-- Omitted: implicit parameters

data RightHandSide e
  = Guarded [(e,e)]       -- f p { | e1 = e2 | e3 = e4 } where ds
  | Normal e              -- f p { = e } where ds
  deriving( Show )

data Statement p e d
  = BindSt p e
  | LetSt [ d ]
  | NoBindSt e
  | ParSt [[Statement p e d]]
  deriving( Show )

data DotDot e = From e | FromThen e e | FromTo e e | FromThenTo e e e 
	      deriving( Show )
  
data Dec 
  = Fun String [Clause Pat Exp Dec]     -- { f p1 p2 = b where decs }
  | Val Pat (RightHandSide Exp) [Dec]   -- { p = b where decs }
  | Data String [String] 
         [Con] [String]         	-- { data T x = A x | B (T x) deriving (Z,W)}
  | TySyn String [String] Typ		-- { type T x = (x,x) }
  | Class Cxt String [String] [Dec]	-- { class Eq a => Ord a where ds }
  | Instance Cxt Typ [Dec]   	 	-- { instance Show w => Show [w] where ds }
  | Proto String Typ                    -- { length :: [a] -> Int }
  | Foreign Foreign
  deriving( Show )

data Foreign = Import Callconv Safety String String Typ
             -- Export missing...
	     deriving( Show )

data Callconv = CCall | StdCall
	      deriving( Show )

data Safety = Unsafe | Safe | Threadsafe
	    deriving( Show )

type Cxt = [Typ]	-- (Eq a, Ord b)

data Con = Constr String [Typ]
         deriving( Show )

data Program = Program [ Dec ] 
             deriving( Show )

-- FIXME: Why this special status for "List" (even tuples might be handled
--	  differently)? -=chak
data Tag = Tuple Int | Arrow | List | TconName String
         deriving (Eq, Show)

data Typ = TForall [String] Cxt Typ  -- forall <vars>. <ctxt> -> <type>
	 | Tvar String               -- a
         | Tcon Tag                  -- T or [] or (->) or (,,) etc
         | Tapp Typ Typ              -- T a b
 	 deriving( Show )
 
---------------------------------------------------
-- Combinator based types

type Expr = Q Exp
type Decl = Q Dec
type Cons = Q Con
type Type = Q Typ
type Patt = Pat		-- No need for Q here
  -- FIXME: I think it is more annoying having an exception here, rather than
  --   wrapping Pat unnecessarily into Q  -=chak
type Ctxt = Q Cxt

type Mat  = Match Pat Exp Dec
type Mtch = Q Mat

type Cls  = Clause Pat Exp Dec
type Clse = Q Cls

type Rhs  = RightHandSide Exp
type Rihs = Q Rhs

type Stm  = Statement Pat Exp Dec
type Stmt = Q Stm

type DDt  = DotDot Exp
type DDot = Q DDt

--runE :: Expr -> Exp
--runE x = runQ 0 x

--runP :: Pattern -> Pat
runP x = x

--runD :: Decl -> Dec
--runD d = runQ 0 d




-------------------- Lowercase pattern syntax functions ---

integerL  = Integer
charL     = Char
stringL   = String
rationalL = Rational

plit = Plit
pvar = Pvar
ptup = Ptup
pcon = Pcon
ptilde = Ptilde
paspat = Paspat
pwild = Pwild


--------------------------------------------------------------------------------
-- 	Stmt

bindSt :: Patt -> Expr -> Stmt
bindSt p e = do { e1 <- e; return (BindSt p e1) }

letSt :: [Decl] -> Stmt
letSt ds = do { ds1 <- sequence ds; return (LetSt ds1) }

noBindSt :: Expr -> Stmt
noBindSt e = do { e1 <- e; return (NoBindSt e1) }

parSt :: [[Stmt]] -> Stmt
parSt zs = fail "No parallel comprehensions yet"

--------------------------------------------------------------------------------
-- 	RightHandSide

normal :: Expr -> Rihs
normal e = do { e1 <- e; return (Normal e1) }

guarded :: [(Expr,Expr)] -> Rihs
guarded gs = do { gs1 <- mapM f gs; return (Guarded gs1) }
	   where
		f (g,e) = do { g1 <- g; e1 <- e; return (g1,e1) }

--------------------------------------------------------------------------------
-- 	Match and Clause

match :: Patt -> Rihs -> [Decl] -> Mtch
match p rhs ds = do { r' <- rhs; ds' <- sequence ds; return (Mat p r' ds') }

clause :: [Patt] -> Rihs -> [Decl] -> Clse
clause ps r ds = do { r' <- r; ds' <- sequence ds; return (Clause ps r' ds') }


---------------------------------------------------------------------------
-- 	Expr

global :: String -> Expr
global s = return (Var s)

var :: String -> Expr
var s = return (Var s)

con :: String -> Expr
con s =  return (Con s)

lit :: Lit -> Expr
lit c = return (Lit c)

app :: Expr -> Expr -> Expr
app x y = do { a <- x; b <- y; return (App a b)}

infixE :: Maybe Expr -> Expr -> Maybe Expr -> Expr
infixE (Just x) s (Just y) = do { a <- x; s' <- s; b <- y; return (Infix (Just a) s' (Just b))}
infixE Nothing  s (Just y) = do { s' <- s; b <- y; return (Infix Nothing s' (Just b))}
infixE (Just x) s Nothing  = do { a <- x; s' <- s; return (Infix (Just a) s' Nothing)}
infixE Nothing  s Nothing  = do { s' <- s; return (Infix Nothing s' Nothing) }

infixApp x y z = infixE (Just x) y (Just z)
sectionL x y = infixE (Just x) y Nothing
sectionR x y = infixE Nothing x (Just y)

from :: Expr -> Expr
from x = do { a <- x; return (ArithSeq (From a)) }  

fromThen :: Expr -> Expr -> Expr
fromThen x y = do { a <- x; b <- y; return (ArithSeq (FromThen a b)) }  

fromTo :: Expr -> Expr -> Expr
fromTo x y = do { a <- x; b <- y; return (ArithSeq (FromTo a b)) }  

fromThenTo :: Expr -> Expr -> Expr -> Expr
fromThenTo x y z = do { a <- x; b <- y; c <- z; return (ArithSeq (FromThenTo a b c)) }  

lam :: [Patt] -> Expr -> Expr
lam ps e = do { e2 <- e ; return (Lam ps e2) }

lam1 :: Patt -> Expr -> Expr	-- Single-arg lambda
lam1 p e = lam [p] e              

tup :: [Expr] -> Expr
tup es = do { es1 <- sequence es; return (Tup es1)}

cond :: Expr -> Expr -> Expr -> Expr
cond x y z =  do { a <- x; b <- y; c <- z; return (Cond a b c)}

letE :: [Decl] -> Expr -> Expr
letE ds e = do { ds2 <- sequence ds; e2 <- e; return (Let ds2 e2) }

caseE :: Expr -> [Mtch] -> Expr
caseE e ms = do { e1 <- e; ms1 <- sequence ms; return (Case e1 ms1) } 

doE :: [Stmt] -> Expr
doE ss = do { ss1 <- sequence ss; return (Do ss1) } 

comp :: [Stmt] -> Expr
comp ss = do { ss1 <- sequence ss; return (Comp ss1) } 

listExp :: [Expr] -> Expr
listExp es = do { es1 <- sequence es; return (ListExp es1) }

sigExp :: Expr -> Type -> Expr
sigExp e t = do { e1 <- e; t1 <- t; return (SigExp e1 t1) }

string :: String -> Expr
string = lit . String

--------------------------------------------------------------------------------
-- 	Decl

val :: Patt -> Rihs -> [Decl] -> Decl
val p b ds = 
  do { ds1 <- sequence ds
     ; b1 <- b
     ; return(Val p b1 ds1)
     }

fun :: String -> [Clse] -> Decl     
fun nm cs = 
 do { cs1 <- sequence cs
    ; return (Fun nm cs1)
    }

tySynD :: String -> [String] -> Type -> Decl
tySynD tc tvs rhs = do { rhs1 <- rhs; return (TySyn tc tvs rhs1) }

dataD :: String -> [String] -> [Cons] -> [String] -> Decl
dataD tc tvs cons derivs
  = do { cons1 <- sequence cons; return (Data tc tvs cons1 derivs) }

classD :: Ctxt -> String -> [String] -> [Decl] -> Decl
classD ctxt cls tvs decs =
  do 
    decs1 <- sequence decs
    ctxt1 <- ctxt
    return $ Class ctxt1 cls tvs decs1

inst :: Ctxt -> Type -> [Decl] -> Decl
inst ctxt ty decs =
  do 
    ctxt1 <- ctxt
    decs1 <- sequence decs
    ty1   <- ty
    return $ Instance ctxt1 ty1 decs1

proto :: String -> Type -> Decl
proto fun ty = liftM (Proto fun) $ ty

ctxt :: [Type] -> Ctxt
ctxt = sequence

constr :: String -> [Type] -> Cons
constr con tys = liftM (Constr con) $ sequence tys


--------------------------------------------------------------------------------
-- 	Type

tforall :: [String] -> Ctxt -> Type -> Type
tforall tvars ctxt ty = do
  do
    ctxt1 <- ctxt
    ty1   <- ty
    return $ TForall tvars ctxt1 ty1

tvar :: String -> Type
tvar = return . Tvar

tcon :: Tag -> Type
tcon = return . Tcon

tapp :: Type -> Type -> Type
tapp t1 t2 = do
	       t1' <- t1
	       t2' <- t2
	       return $ Tapp t1' t2'

arrowTyCon :: Type
arrowTyCon = return $ Tcon Arrow

listTyCon :: Type
listTyCon = return $ Tcon List

tupleTyCon :: Int -> Type
tupleTyCon i = return $ Tcon (Tuple i)

namedTyCon :: String -> Type
namedTyCon s = return $ Tcon (TconName s)

--------------------------------------------------------------
-- useful helper functions

combine pairs = foldr f ([],[]) pairs
  where f (env,p) (es,ps) = (env++es,p:ps)

rename (Plit c)  = return([],Plit c)
rename (Pvar s)  = do { s1 <- gensym s; return([(s,s1)],Pvar s1) }
rename (Ptup ps) = do { pairs <- mapM rename ps; g(combine pairs) }
   where g (es,ps) = return (es,Ptup ps)
rename (Pcon nm ps) = do { pairs <- mapM rename ps; g(combine pairs) }
   where g (es,ps) = return (es,Pcon nm ps)
rename (Ptilde p) = do { (env,p2) <- rename p; return(env,Ptilde p2) }   
rename (Paspat s p) = 
   do { s1 <- gensym s; (env,p2) <- rename p; return((s,s1):env,Paspat s1 p2) }
rename Pwild = return([],Pwild)

genpat p = do { (env,p2) <- rename p; return(alpha env,p2) }

alpha env s = case lookup s env of
               Just x -> return(Var x)
               Nothing -> return(Var s)

--genPE s n = [ (pvar x, var x) | i <- [1..n], let x = s ++ show i ]

genPE s n = let ns = [ s++(show i) | i <- [1..n]]
            in (map pvar ns,map var ns)

apps :: [Expr] -> Expr
apps [x] = x
apps (x:y:zs) = apps ( (app x y) : zs )

simpleM :: Pat -> Exp -> Mat
simpleM p e = Mat p (Normal e) []


--------------------------------------------------------------
-- 		A pretty printer (due to Ian Lynagh)
--------------------------------------------------------------

nestDepth :: Int
nestDepth = 4

type Precedence = Int
appPrec, opPrec, noPrec :: Precedence
appPrec = 2	-- Argument of a function application
opPrec  = 1	-- Argument of an infix operator
noPrec  = 0	-- Others

parensIf :: Bool -> Doc -> Doc
parensIf True d = parens d
parensIf False d = d

------------------------------
pprExp :: Exp -> Doc
pprExp = pprExpI noPrec

pprExpI :: Precedence -> Exp -> Doc
pprExpI _ (Var v)     = text v
pprExpI _ (Con c)     = text c
pprExpI i (Lit l)     = pprLit i l
pprExpI i (App e1 e2) = parensIf (i >= appPrec) $ pprExpI opPrec e1
                                        <+> pprExpI appPrec e2
pprExpI i (Infix (Just e1) op (Just e2))
 = parensIf (i >= opPrec) $ pprExpI opPrec e1
                          <+> pprExp op
                          <+> pprExpI opPrec e2
pprExpI _ (Infix me1 op me2) = parens $ pprMaybeExp noPrec me1
                                    <+> pprExp op
                                    <+> pprMaybeExp noPrec me2
pprExpI i (Lam ps e) = parensIf (i > noPrec) $ char '\\'
                                       <> hsep (map pprPat ps)
                                      <+> text "->" <+> pprExp e
pprExpI _ (Tup es) = parens $ sep $ punctuate comma $ map pprExp es
-- Nesting in Cond is to avoid potential problems in do statments
pprExpI i (Cond guard true false)
 = parensIf (i > noPrec) $ sep [text "if" <+> pprExp guard,
                           nest 1 $ text "then" <+> pprExp true,
                           nest 1 $ text "else" <+> pprExp false]
pprExpI i (Let ds e) = parensIf (i > noPrec) $ text "let" <+> vcat (map pprDec ds)
                                       $$ text " in" <+> pprExp e
pprExpI i (Case e ms)
 = parensIf (i > noPrec) $ text "case" <+> pprExp e <+> text "of"
                   $$ nest nestDepth (vcat $ map pprMatch ms)
pprExpI i (Do ss) = parensIf (i > noPrec) $ text "do"
                                   <+> vcat (map pprStatement ss)
pprExpI _ (Comp []) = error "Can't happen: pprExpI (Comp [])"
-- This will probably break with fixity declarations - would need a ';'
pprExpI _ (Comp ss) = text "[" <> pprStatement s
                  <+> text "|"
                  <+> (sep $ punctuate comma $ map pprStatement ss')
                   <> text "]"
  where s = last ss
        ss' = init ss
pprExpI _ (ArithSeq d) = pprDotDot d
pprExpI _ (ListExp es) = brackets $ sep $ punctuate comma $ map pprExp es
	-- 5 :: Int :: Int will break, but that's a silly thing to do anyway
pprExpI i (SigExp e t)
 = parensIf (i > noPrec) $ pprExp e <+> text "::" <+> pprTyp t

pprMaybeExp :: Precedence -> Maybe Exp -> Doc
pprMaybeExp _ Nothing = empty
pprMaybeExp i (Just e) = pprExpI i e

------------------------------
pprStatement :: Statement Pat Exp Dec -> Doc
pprStatement (BindSt p e) = pprPat p <+> text "<-" <+> pprExp e
pprStatement (LetSt ds) = text "let" <+> vcat (map pprDec ds)
pprStatement (NoBindSt e) = pprExp e
pprStatement (ParSt sss) = sep $ punctuate (text "|")
                         $ map (sep . punctuate comma . map pprStatement) sss

------------------------------
pprMatch :: Match Pat Exp Dec -> Doc
pprMatch (Mat p rhs ds) = pprPat p <+> pprRhs False rhs
                       $$ where_clause ds

------------------------------
pprRhs :: Bool -> RightHandSide Exp -> Doc
pprRhs eq (Guarded xs) = nest nestDepth $ vcat $ map do_guard xs
  where eqd = if eq then text "=" else text "->"
        do_guard (lhs, rhs) = text "|" <+> pprExp lhs <+> eqd <+> pprExp rhs
pprRhs eq (Normal e) = (if eq then text "=" else text "->")
                       <+> pprExp e

------------------------------
pprLit :: Precedence -> Lit -> Doc
pprLit i (Integer x) = parensIf (i > noPrec && x < 0) (integer x)
pprLit _ (Char c) = text (show c)
pprLit _ (String s) = text (show s)
pprLit i (Rational rat) = parensIf (i > noPrec) $ text $ show rat

------------------------------
pprPat :: Pat -> Doc
pprPat = pprPatI noPrec

pprPatI :: Precedence -> Pat -> Doc
pprPatI i (Plit l)     = pprLit i l
pprPatI _ (Pvar v)     = text v
pprPatI _ (Ptup ps)    = parens $ sep $ punctuate comma $ map pprPat ps
pprPatI i (Pcon s ps)  = parensIf (i > noPrec) $ text s <+> sep (map (pprPatI appPrec) ps)
pprPatI i (Ptilde p)   = parensIf (i > noPrec) $ pprPatI appPrec p
pprPatI i (Paspat v p) = parensIf (i > noPrec) $ text v <> text "@" <> pprPatI appPrec p
pprPatI _ Pwild = text "_"

------------------------------
pprDec :: Dec -> Doc
pprDec (Fun f cs)   = vcat $ map (\c -> text f <+> pprClause c) cs
pprDec (Val p r ds) = pprPat p <+> pprRhs True r
                      $$ where_clause ds
pprDec (TySyn t xs rhs) = text "type" <+> text t <+> hsep (map text xs) 
				<+> text "=" <+> pprTyp rhs
pprDec (Data t xs cs ds) = text "data" <+> text t <+> hsep (map text xs)
                       <+> text "=" <+> sep (map pprCon cs)
                        $$ if null ds
                           then empty
                           else nest nestDepth
                              $ text "deriving"
                            <+> parens (hsep $ punctuate comma $ map text ds)
pprDec (Class cxt c xs ds) = text "class" <+> pprCxt cxt
                         <+> text c <+> hsep (map text xs)
                          $$ where_clause ds
pprDec (Instance cxt i ds) = text "instance" <+> pprCxt cxt <+> pprTyp i
                          $$ where_clause ds
pprDec (Proto f t) = text f <+> text "::" <+> pprTyp t
pprDec (Foreign f) = pprForeign f

------------------------------
pprForeign :: Foreign -> Doc
pprForeign (Import callconv safety impent as typ) = text "foreign import"
                                                <+> showtextl callconv
                                                <+> showtextl safety
                                                <+> text (show impent)
                                                <+> text as
                                                <+> text "::" <+> pprTyp typ

------------------------------
pprClause :: Clause Pat Exp Dec -> Doc
pprClause (Clause ps rhs ds) = hsep (map pprPat ps) <+> pprRhs True rhs
                            $$ where_clause ds

------------------------------
pprCon :: Con -> Doc
pprCon (Constr c ts) = text c <+> hsep (map pprTyp ts)

------------------------------
pprParendTyp :: Typ -> Doc
pprParendTyp (Tvar s) = text s
pprParendTyp (Tcon t) = pprTcon t
pprParendTyp other    = parens (pprTyp other)

pprTyp :: Typ -> Doc
pprTyp (TForall tvars ctxt ty) = 
  text "forall" <+> hsep (map text tvars) <+> text "." <+> 
  ctxtDoc <+> pprTyp ty
  where
    ctxtDoc | null ctxt = empty
	    | otherwise = parens (sep (punctuate comma (map pprTyp ctxt))) <+>
			  text "=>"
pprTyp ty		       = pprTyApp (split ty)

pprTyApp (Tcon Arrow, [arg1,arg2])
  = sep [pprTyp arg1 <+> text "->", pprTyp arg2]

pprTyApp (Tcon List, [arg])
  = brackets (pprTyp arg)

pprTyApp (Tcon (Tuple n), args)
  | length args == n
  = parens (sep (punctuate comma (map pprTyp args)))

pprTyApp (fun, args)
  = pprParendTyp fun <+> sep (map pprParendTyp args)

pprTcon :: Tag -> Doc
pprTcon (Tuple 0)    = text "()"
pprTcon (Tuple n)    = parens (hcat (replicate (n-1) comma))
pprTcon Arrow	     = parens (text "->")
pprTcon List	     = text "[]"
pprTcon (TconName s) = text s

split :: Typ -> (Typ, [Typ])	-- Split into function and args
split t = go t []
	where
	  go (Tapp t1 t2) args = go t1 (t2:args)
	  go ty		  args = (ty, args)

------------------------------
pprCxt :: Cxt -> Doc
pprCxt [] = empty
pprCxt [t] = pprTyp t <+> text "=>"
pprCxt ts = parens (hsep $ punctuate comma $ map pprTyp ts) <+> text "=>"

------------------------------
pprDotDot :: DotDot Exp -> Doc
pprDotDot = brackets . pprDotDotI

pprDotDotI :: DotDot Exp -> Doc
pprDotDotI (From e) = pprExp e <> text ".."
pprDotDotI (FromThen e1 e2) = pprExp e1 <> text ","
                           <> pprExp e2 <> text ".."
pprDotDotI (FromTo e1 e2) = pprExp e1 <> text ".." <> pprExp e2
pprDotDotI (FromThenTo e1 e2 e3) = pprExp e1 <> text ","
                                <> pprExp e2 <> text ".."
                                <> pprExp e3

------------------------------
where_clause :: [Dec] -> Doc
where_clause [] = empty
where_clause ds = text "where" <+> vcat (map pprDec ds)

showtextl :: Show a => a -> Doc
showtextl = text . map toLower . show
