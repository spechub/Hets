-- Invader.hs

-----------------------------------------------------------------------------
-- Library of functions for writing interactive programs with screen-oriented
-- I/O (assumes Ansi screen).
--
-- Suitable for use with Hugs 98.
-----------------------------------------------------------------------------

module Main where

--import System
--import Random
--import IOExts
--import IO

{-
module AnsiInteract(
	module AnsiInteract,
	module Interact,
	module AnsiScreen
	) where

import AnsiScreen
import Interact
-}

-- Screen oriented input/output functions:


clearScreen       :: Interact -> Interact
writeAt           :: Pos -> String -> Interact -> Interact
moveTo            :: Pos -> Interact -> Interact
readAt            :: Pos                  ->  -- Start coordinates
                     Int                  ->  -- Maximum input length
                     (String -> Interact) ->  -- How to use entered string
                     Interact
defReadAt         :: Pos                  ->  -- Start coordinates        
                     Int                  ->  -- Maximum input length     
                     String               ->  -- Default string value     
                     (String -> Interact) ->  -- How to use entered string
                     Interact
promptReadAt      :: Pos                  -> -- Start coordinates        
                     Int                  -> -- Maximum input length     
                     String               -> -- Prompt
                     (String -> Interact) -> -- How to use entered string
                     Interact
defPromptReadAt   :: Pos                  -> -- Start coordinates        
                     Int                  -> -- Maximum input length     
                     String               -> -- Prompt
                     String               -> -- Default string value
                     (String -> Interact) -> -- How to use entered string
                     Interact


clearScreen        = writeStr cls
writeAt (x,y) s    = writeStr (goto x y ++ s)
moveTo  (x,y)      = writeStr (goto x y)


readAt pt l use    = writeAt pt (replicate l '_') (moveTo pt (loop 0 ""))
 where loop n s    = readChar (return s) (\c ->
                     case c of '\BS'         -> delete n s
                               '\DEL'        -> delete n s
                               '\n'          -> return s
                               c | n < l     -> writeChar c (loop (n+1) (c:s))
                                 | otherwise -> ringBell (loop n s))
       delete n s  = if n>0 then writeStr "\BS_\BS" (loop (n-1) (tail s))
                            else ringBell (loop 0 "")
       return s    = use (reverse s)


defReadAt (x,y) l def use
                   = writeAt (x,y) (take l (def++repeat '_')) (
                     readChar (use def) (\c ->
                     if c=='\n' then use def
                                else unreadChar c (readAt (x,y) l use)))

promptReadAt (x,y) l prompt use
                   = writeAt (x,y) prompt (readAt (x+length prompt,y) l use)

defPromptReadAt (x,y) l prompt def use
                   = writeAt (x,y) prompt (
                     defReadAt (x+length prompt,y) l def use)

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
-- Library of escape sequences for ANSI compatible screen I/O:
--
-- Suitable for use with Hugs 98
-----------------------------------------------------------------------------

{-
module AnsiScreen(
	Pos(..),
	cls,
	goto, at, home, 
	highlight
	) where
-}

-- Basic screen control codes:


type Pos           = (Int,Int)

at        :: Pos -> String -> String
highlight :: String -> String
goto      :: Int -> Int -> String
home      :: String
cls       :: String


at (x,y) s  = goto x y ++ s
highlight s = "\ESC[7m"++(s++"\ESC[0m")
goto x y    = '\ESC':('[':(show y ++(';':show x ++ "H")))
home        = goto 1 1

-- Choose whichever of the following lines is suitable for your system:
cls         = "\ESC[2J"     -- for PC with ANSI.SYS
--cls         = "\^L"         -- for Sun window

-----------------------------------------------------------------------------
{-
module Draw where

import AnsiInteract
import Sprite
-}

drawSprite :: Sprite -> Interact -> Interact

drawSprite (Sprite coord gunOffset images imageIndex maxImageIndex vis _ _ _) i
   | vis = drawSpriteImage (images!!imageIndex) coord i
   | otherwise = i 

drawSpriteImage :: SpriteImage -> Coordinate -> Interact -> Interact

drawSpriteImage pixels (x,y)
   = interactList ( map (\((a,b),c) -> safeWritePixel (a,b) c) (map (\((a,b), c) -> ((x+a, y+b), c)) pixels))

blankSprite :: Sprite -> Interact -> Interact

blankSprite (Sprite coord gunOffset images imageIndex maxImageIndex vis _ _ _) i
   | vis = blankSpriteImage (images!!imageIndex) coord i
   | otherwise = i

blankSpriteImage :: SpriteImage -> Coordinate -> Interact -> Interact

blankSpriteImage pixels (x,y)
   = interactList ( map (\((a,b),_) -> safeWritePixel (a,b) ' ') ( map (\((a,b), c) -> ((x+a, y+b), c)) pixels))

safeWritePixel :: Coordinate -> Char -> Interact -> Interact
safeWritePixel (x,y) c i
   | (x < 1) || (x > 80) || (y < 1) || (y > 40) = i
   | otherwise = writeAt (x,y) [c] (moveTo (1,1) i)

runI :: Interact -> IO ()
runI i = putStr $ i ""

interactList :: [Interact -> Interact] -> Interact -> Interact
interactList xs i = foldr id i xs

{-
moveSprite :: Sprite -> Coordinate -> Interact -> Interact

moveSprite (Sprite (sx,sy) gunOffset images imageNumber vis) (x,y) i
   = interactList [blankSprite (Sprite (sx,sy) gunOffset images imageNumber vis),
                   drawSprite  (Sprite (x,y) gunOffset images imageNumber vis)] i
-}

pause :: Int -> Interact -> Interact
pause speed i
   | speed < 0 = error "The speed value must be non-negative"
   | otherwise = seq (fib speed) i

fib :: Int -> Int
fib 0 = 1
fib 1 = 1
fib n = (fib (n-1)) + (fib (n-2))
-----------------------------------------------------------------------------
-- Library for simple interactive programs:
--
-- Suitable for use with Hugs 98
-----------------------------------------------------------------------------

{-
module Interact(
	Interact(..),
	end,
	readChar, peekChar, unreadChar, pressAnyKey,
	writeChar, writeStr,
	readLine,
	ringBell
	) where
-}

--- Interactive program combining forms:


type Interact = String -> String


end                      :: Interact
readChar, peekChar       :: Interact -> (Char -> Interact) -> Interact
pressAnyKey              :: Interact -> Interact
unreadChar               :: Char -> Interact -> Interact
writeChar                :: Char -> Interact -> Interact
writeStr                 :: String -> Interact -> Interact
ringBell                 :: Interact -> Interact
readLine                 :: String -> (String -> Interact) -> Interact


end cs                    = ""

readChar eof use []       = eof []
readChar eof use (c:cs)   = use c cs

peekChar eof use []       = eof []     -- like readChar, but character is
peekChar eof use cs@(c:_) = use c cs   -- not removed from input stream

pressAnyKey prog          = readChar prog (\c -> prog)

unreadChar c prog cs      = prog (c:cs)

writeChar c prog cs       = c : prog cs

writeStr s prog cs        = s ++ prog cs

ringBell                  = writeChar '\BEL'

readLine prompt g is  = prompt ++ lineOut 0 line ++ "\n"
                               ++ g (noBackSpaces line) input'
 where line     = before '\n' is
       input'   = after  '\n' is
       after x  = tail . dropWhile (x/=)
       before x = takeWhile (x/=)

       rubout  :: Char -> Bool
       rubout c = ((c=='\DEL') || (c=='\BS'))

       lineOut                      :: Int -> String -> String
       lineOut n ""                  = ""
       lineOut n (c:cs)
                 | n>0  && rubout c  = "\BS \BS" ++ lineOut (n-1) cs
                 | n==0 && rubout c  = lineOut 0 cs
                 | otherwise         = c:lineOut (n+1) cs

       noBackSpaces :: String -> String
       noBackSpaces  = reverse . delete 0 . reverse
                       where delete n ""          = ""
                             delete n (c:cs)
                                      | rubout c  = delete (n+1) cs
                                      | n>0       = delete (n-1) cs
                                      | otherwise = c:delete 0 cs

{-
-----------------------------------------------------------------------------

module Main where

import IO

import IOExts
import Sprite
import Draw
import Interact
import AnsiInteract

import System
import Random
-}


type Tick = Int
type Gun = Sprite
type Bullets = [Sprite]
type Invaders = [Sprite]
type Explosions = [Sprite]
type Score = Int 
type Lives = Int
type Level = Int


-- GameState = (time tick, gun sprite, gun bullet sprites, invader sprites, invader bullet sprites explosion sprites)
type GameState = (Tick, Gun, Bullets, Invaders, Bullets, Explosions, Score, Lives, Level)

getTick :: GameState -> Tick
getTick (t, _, _, _, _, _, _, _, _) = t

getGun :: GameState -> Gun 
getGun (_, g, _, _, _, _, _, _, _) = g

getGunBullets :: GameState -> Bullets 
getGunBullets (_, _, bs, _, _, _, _, _, _) = bs 

getInvaders :: GameState -> Invaders 
getInvaders (_, _, _, is, _, _, _, _, _) = is 

getInvBullets :: GameState -> Bullets 
getInvBullets (_, _, _, _, ib, _, _, _, _) = ib 

getExplosions :: GameState -> Explosions 
getExplosions (_, _, _, _, _, es, _, _, _) = es 

getScore :: GameState -> Score 
getScore (_, _, _, _, _, _, s, _, _) = s

getLives :: GameState -> Lives 
getLives (_, _, _, _, _, _, _, l, _) = l

getLevel :: GameState -> Level 
getLevel (_, _, _, _, _, _, _, _, l) = l

makeGameState :: Tick -> Gun -> Bullets -> Invaders -> Bullets -> Explosions -> Score -> Lives -> Level -> GameState 
makeGameState tick gun gunBullets invaders invBullets explosions score lives level
   = (tick, gun, gunBullets, invaders, invBullets, explosions, score, lives, level)

modifyTickInState :: GameState -> Tick -> GameState
modifyTickInState (oldTick, gun, gunBullets, invaders, invBullets, explosions, score, lives, level) newTick
   = (newTick, gun, gunBullets, invaders, invBullets, explosions, score, lives, level)

modifyGunInState :: GameState -> Gun -> GameState
modifyGunInState (tick, oldGun, gunBullets, invaders, invBullets, explosions, score, lives, level) newGun 
   = (tick, newGun, gunBullets, invaders, invBullets, explosions, score, lives, level)

modifyGunBulletsInState :: GameState -> Bullets -> GameState
modifyGunBulletsInState (tick, gun, oldGunBullets, invaders, invBullets, explosions, score, lives, level) newGunBullets
   = (tick, gun, newGunBullets, invaders, invBullets, explosions, score, lives, level)

modifyInvadersInState :: GameState -> Invaders -> GameState
modifyInvadersInState (tick, gun, gunBullets, oldInvaders, invBullets, explosions, score, lives, level) newInvaders
   = (tick, gun, gunBullets, newInvaders, invBullets, explosions, score, lives, level)

modifyInvBulletsInState :: GameState -> Bullets -> GameState
modifyInvBulletsInState (tick, gun, gunBullets, invaders, oldInvBullets, explosions, score, lives, level) newInvBullets
   = (tick, gun, gunBullets, invaders, newInvBullets, explosions, score, lives, level)

modifyExpsInState :: GameState -> Explosions -> GameState
modifyExpsInState (tick, gun, gunBullets, invaders, invBullets, oldExplosions, score, lives, level) newExplosions
   = (tick, gun, gunBullets, invaders, invBullets, newExplosions, score, lives, level)

modifyScoreInState :: GameState -> Score -> GameState
modifyScoreInState (tick, gun, gunBullets, invaders, invBullets, explosions, oldScore, lives, level) newScore
   = (tick, gun, gunBullets, invaders, invBullets, explosions, newScore, lives, level)

modifyLivesInState :: GameState -> Lives -> GameState
modifyLivesInState (tick, gun, gunBullets, invaders, invBullets, explosions, score, oldLives, level) newLives 
   = (tick, gun, gunBullets, invaders, invBullets, explosions, score, newLives, level)

modifyLevelInState :: GameState -> Level -> GameState
modifyLevelInState (tick, gun, gunBullets, invaders, invBullets, explosions, score, lives, oldLevel) newLevel
   = (tick, gun, gunBullets, invaders, invBullets, explosions, score, lives, newLevel)

-- time delays for various events. The ints correspond to the number of time ticks
-- that must occur before an event is triggered.

bulletDelay :: Int
bulletDelay = 5

explosionDelay :: Int
explosionDelay = 10 

invaderMoveDelay :: Int
invaderMoveDelay = 20 

invBulletSpawnDelay :: Int
invBulletSpawnDelay = 50  

readKeyBoard :: Int -> IO (Maybe Char)

readKeyBoard delay
   = do
        -- isInputReady <- hWaitForInput stdin delay 
        let isInputReady = True 
        if isInputReady then do
                              -- nextChar <- hGetChar stdin
                              nextChar <- getChar 
                              return (Just nextChar)
                        else return Nothing

loopInput :: GameState -> IO ()
loopInput _ = return ()


loopInput gameState 
   = do
       nextChar <- readKeyBoard 100
       let tick = getTick gameState
       let newTick = if tick == 100000 then 0 else tick + 1
       let newGameState = modifyTickInState gameState newTick
       case nextChar of
          Just 'q'  -> quit 
          Just ' '  -> do
                          let gunSprite = getGun gameState
                          let bullets = getGunBullets gameState
                          let nb = newGunBullet $ spriteGunXY gunSprite
                          runDraw nb 
                          let newGameState' = modifyGunBulletsInState newGameState (nb:bullets)
                          moveGunSprite nextChar newGameState' 
          _         -> moveGunSprite nextChar newGameState 

moveGunSprite :: Maybe Char -> GameState -> IO ()  

moveGunSprite nextChar gameState 
   = do
        let gunSprite = getGun gameState
        case nextChar of 
           Just '.' -> do
                          let rightGunSprite = moveSprite (1,0) gunSprite
                          runBlank gunSprite 
                          runDraw  rightGunSprite
                          let newGameState = modifyGunInState gameState rightGunSprite
                          collisions newGameState 
           Just ',' -> do
                          let leftGunSprite = moveSprite (-1,0) gunSprite
                          runBlank gunSprite 
                          runDraw leftGunSprite
                          let newGameState = modifyGunInState gameState leftGunSprite
                          collisions newGameState 
           _        -> collisions gameState 


collisions :: GameState -> IO ()

collisions gameState 
   = do
        let tick = getTick gameState
        case (tick `mod` bulletDelay == 0) of
           True -> do
                   let gunBullets = getGunBullets gameState
                   let invaders = getInvaders gameState
                   let explosions = getExplosions gameState
                   let gun = getGun gameState
                   let invBullets = getInvBullets gameState
                   let score = getScore gameState
                   let lives = getLives gameState
                   let (remGunBullets, remInvaders, collisions) = bulletInvaderCollide gunBullets invaders
                   let newInvExplosions = map (\coord -> newExplosion coord) collisions
                   let remInvBullets = bulletGunCollide invBullets gun
                   let isGunHit = length remInvBullets < length invBullets
                   let (newGunExplosion, newLives) = case isGunHit of
                                                        True -> ([newExplosion $ spriteXY gun], lives - 1)
                                                        False -> ([], lives)
                   if newLives == 0 then quit else return ()
                   if isGunHit then (runI $ writeAt (1,42) ("Lives: " ++ show newLives) end) else return ()
                   sequence_ $ map runDraw (newGunExplosion ++ newInvExplosions)
                   let newGameState1 = modifyExpsInState gameState (newGunExplosion ++ newInvExplosions ++ explosions)
                   let newGameState2 = modifyInvadersInState newGameState1 remInvaders 
                   let newGameState3 = modifyGunBulletsInState newGameState2 remGunBullets 
                   let newScore = 1000 * length collisions
                   if newScore /= 0 then (runI $ writeAt (1,41) ("Score: " ++ (show (score + newScore))) end) else return ()
                   let newGameState4 = modifyScoreInState newGameState3 (score + newScore)
                   let newGameState5 = modifyLivesInState newGameState4 newLives 
                   let newGameState6 = modifyInvBulletsInState newGameState5 remInvBullets 
                   updateExplosions newGameState6
           False -> updateExplosions gameState

updateExplosions :: GameState -> IO ()

updateExplosions gameState 
  = do
       let tick = getTick gameState 
       let explosions = getExplosions gameState
       case (tick `mod` explosionDelay == 0) of
          True -> do
                     let visibleExplosions = filter (not . explodeFinish) explosions
                     let newExplosions = map changeExplosImg visibleExplosions 
                     sequence_ $ map runBlank explosions 
                     sequence_ $ map runDraw  newExplosions 
                     let newGameState = modifyExpsInState gameState newExplosions
                     moveBullets newGameState
          False -> moveBullets gameState 

changeExplosImg :: Sprite -> Sprite 
changeExplosImg (Sprite coord gunOffset images imgIndex maxIndex vis motion motIndex maxMot)
   = Sprite coord gunOffset images (imgIndex+1) maxIndex vis motion motIndex maxMot

explodeFinish :: Sprite -> Bool 
explodeFinish (Sprite coord gunOffset images imgIndex maxIndex vis motion motIndex maxMot)
   = imgIndex == maxIndex 

bulletInvaderCollide :: Bullets -> Invaders -> (Bullets, Invaders, [Coordinate]) 
bulletInvaderCollide [] invaders 
   = ([], invaders, []) 


bulletInvaderCollide (b:bs) invaders
   = case collideAny b invaders [] of
        Nothing -> let (restBs, restInvaders, restColls) = bulletInvaderCollide bs invaders
                   in (b:restBs, restInvaders, restColls)
        Just (survivers, collision) -> let (restBs, restInvaders, restColls) = bulletInvaderCollide bs survivers
                                       in (restBs, restInvaders, collision:restColls)
   where
   collideAny :: Sprite -> [Sprite] -> [Sprite] -> Maybe ([Sprite], Coordinate)
   collideAny bullet [] acc = Nothing 
   collideAny bullet (inv:invs) acc
      = if spriteXY bullet == spriteXY inv 
        then Just ((acc ++ invs), spriteXY inv)
        else collideAny bullet invs (inv:acc)

bulletGunCollide :: Bullets -> Gun -> Bullets 
bulletGunCollide [] _ = [] 
bulletGunCollide (b:bs) gun
   | spriteXY b == spriteXY gun = bs 
   | otherwise = b : bulletGunCollide bs gun 


moveBullets :: GameState -> IO ()


moveBullets gameState 
   = do
        let gunBullets = getGunBullets gameState
        let invBullets = getInvBullets gameState
        let tick = getTick gameState
        let visibleGunBullets = takeWhile (\s -> spriteY s > 0) gunBullets
        let visibleInvBullets = takeWhile (\s -> spriteY s <= 40) invBullets
        case (tick `mod` bulletDelay == 0) of
           True -> do
                      let movedGunBullets = moveSprites (0,-1) visibleGunBullets
                      sequence_ $ map runBlank gunBullets
                      sequence_ $ map runDraw movedGunBullets
                      let newGameState1 = modifyGunBulletsInState gameState movedGunBullets

                      let movedInvBullets = moveSprites (0,1) visibleInvBullets
                      sequence_ $ map runBlank invBullets
                      sequence_ $ map runDraw movedInvBullets
                      let newGameState2 = modifyInvBulletsInState newGameState1 movedInvBullets

                      moveInvaders newGameState2 
           False -> do
                      let newGameState1 = modifyGunBulletsInState gameState visibleGunBullets
                      let newGameState2 = modifyInvBulletsInState newGameState1 visibleInvBullets
                      moveInvaders newGameState2 

moveInvaders :: GameState -> IO ()

moveInvaders gameState 
   = do
        let invaders = getInvaders gameState
        let tick = getTick gameState
        let visibleInvaders = filter (\i -> spriteY i < 42) invaders
        if isEmpty (visibleInvaders) then nextLevel gameState else return ()
        case (tick `mod` invaderMoveDelay == 0) of
        
           True -> do
                      let invadersMoved = map updateInvaderPosAndImg visibleInvaders
                      sequence_ $ map runBlank invaders
                      sequence_ $ map runDraw invadersMoved
                      let newState = modifyInvadersInState gameState invadersMoved
                      spawnInvaderBullets newState 
                      return ()


           False -> do
                      let newState = modifyInvadersInState gameState visibleInvaders
                      spawnInvaderBullets newState 
                      return ()



spawnInvaderBullets :: GameState -> IO ()

spawnInvaderBullets gameState
   = do
        let invaders = getInvaders gameState
        let invBullets = getInvBullets gameState 
        let tick = getTick gameState
        case (tick `mod` invBulletSpawnDelay == 0) of
           True -> do
                      randomInvader <- randomInRange 0 ((length invaders) - 1)
                      let bulletCoord = spriteGunXY (invaders !! randomInvader)
                      let newState = modifyInvBulletsInState gameState ((newInvBullet bulletCoord):invBullets)
                      loopInput newState
           False -> loopInput gameState 
                   

updateInvaderPosAndImg :: Sprite -> Sprite

updateInvaderPosAndImg (Sprite (sx,sy) gunOffset images imageIndex maxImIndex vis mSeq mInd maxInd)
   = Sprite (sx + xOffset, sy + yOffset) gunOffset images newImgIndex maxImIndex vis mSeq newMotIndex maxInd
   where
   newMotIndex = if mInd == maxInd then 0 else mInd + 1
   (xOffset, yOffset) = mSeq !! mInd
   newImgIndex = if imageIndex == maxImIndex then 0 else imageIndex + 1  
   


moveSprites :: Coordinate -> [Sprite] -> [Sprite]
moveSprites (dx,dy) sprites = map (moveSprite (dx,dy)) sprites

main :: IO ()

main 
   = do 
        -- hSetBuffering stdin NoBuffering 
        -- hSetBuffering stdout NoBuffering 
        -- hSetEcho stdout False
        let initLives = 3
        let initScore = 0
        let initLevel = 1
        nextLevel $ makeGameState 0 exampleGunSprite2 [] initInvaders [] [] initScore initLives initLevel



runBlank :: Sprite -> IO ()
runBlank s = runI (blankSprite s end)

runDraw :: Sprite -> IO ()
runDraw s = runI (drawSprite s end)

nextLevel :: GameState -> IO ()
nextLevel gameState
   = do
        let level = getLevel gameState
        let score = getScore gameState
        let lives = getLives gameState
        let gun = getGun gameState
        let action1 = writeAt (20,20) ("Space Invaders: level " ++ show level)
        let action2 = writeAt (20,21) "Press any key to start" 
        runI ( clearScreen ( action1 ( action2 end ))) 
        nextKey <- readKeyBoard 10000
        case nextKey of
           Just 'q' -> quit
           _        -> do 
                          runI $ clearScreen end 
                          runDraw gun
                          runI $ writeAt (1,41) ("Score: " ++ show score) end
                          runI $ writeAt (1,42) ("Lives: " ++ show lives) end
                          runI $ writeAt (1,43) ("Level: " ++ show level) end
                          let newGameState1 = modifyLevelInState gameState (level + 1)
                          let newGameState2 = modifyInvadersInState newGameState1 initInvaders 
                          loopInput newGameState2 

-- quit :: IO ()

quit 
   = do
        let action1 = writeAt (20,20) "Game Over"
        let action2 = writeAt (20,22) "Thankyou for playing space invaders"
        let action3 = writeAt (20,23) "The planet is once again safe"
        let action4 = moveTo (1,1)
        runI ( clearScreen ( action1 ( action2 ( action3 ( action4 end )))))
        -- exitWith ExitSuccess 


-- initInvaders :: [Sprite]
initInvaders 
   = row1 ++ row2 ++ row3 
   where
   row1 = [newInvader (x, 1) | x <- [5,15..65]]
   row2 = [newInvader (x, 3) | x <- [10,20..70]]
   row3 = [newInvader (x, 5) | x <- [5,15..65]]

-- randomInRange :: Int -> Int -> IO Int
-- randomInRange lo hi = getStdRandom (randomR (lo, hi))

randomInRange lo hi = return ( (lo + hi) `div` 2)


-- module Sprite where

data Sprite
   = Sprite 
        Coordinate        -- position of the sprite (x,y)
        Coordinate        -- position of the gun relative to the above coord
        [SpriteImage]     -- a list of the images for this sprite
        -- [[((Int, Int), Char)]]     -- a list of the images for this sprite
        Int               -- current image index 
        Int               -- max image index
        Bool              -- True=visible, False=invisible
        [Coordinate]      -- motion sequence
        Int               -- current motion index
        Int               -- max motion index
    deriving (Eq, Show)

type Coordinate = (Int, Int)


-- (offset from sprite coordiate, pixel) 
type SpriteImage = [(Coordinate,Char)]

triangleImage :: SpriteImage
triangleImage = [                            ((0,0), '#'),
                               ((-1,1), '#'), ((0,1), '#'), ((1,1), '#'),
                 ((-2,2), '#'), ((-1,2), '#'), ((0,2), '#'), ((1,2), '#'), ((2,2), '#')
                ]

gunBulletImage :: SpriteImage
gunBulletImage = [((0,0), '|')]
invBulletImage :: SpriteImage
invBulletImage = [((0,0), '*')]

exampleGunSprite1 = Sprite (20,40) (0,-1) [triangleImage] 0 0 True [] 0 0

smallImage :: SpriteImage
smallImage =    [                            ((0,0), '#'),
                               ((-1,1), '#'), ((0,1), '#'), ((1,1), '#')
                ]

exampleGunSprite2 = Sprite (20,39) (0,-1) [smallImage] 0 0 True [] 0 0

invaderImage1 :: SpriteImage
invaderImage1 = [((-1,0), '('), ((0,0), '*'), ((1,0), ')'),
                 ((-1,1), '/'), ((1,1), '\\')]

invaderImage2 :: SpriteImage
invaderImage2 = [((-1,0), '('), ((0,0), '*'), ((1,0), ')'),
                 ((0,1), 'V')]

invaderMotion :: [(Int, Int)]
invaderMotion 
   = [(1,0), (1,0), (1,0), (1,0), (0,1), (-1,0), (-1,0), (-1,0), (-1,0), (0,1)]

explodeImage1 :: SpriteImage
explodeImage1 = [ ((0,0), '+')]

explodeImage2 :: SpriteImage
explodeImage2 = [ ((0,-1), '+'),
                  ((-1,0), '+'), ((0,0), '+'), ((1,0), '+'),
                  ((0,1), '+')
                ]

explodeImage3 :: SpriteImage
explodeImage3 = [ ((-1,-1), '.'), ((0,-1), '+'), ((1,-1), '.'),
                  ((-1,0), '+'),  ((1,0), '+'),
                  ((-1,1), '.'), ((0,1), '+'), ((1,1), '.')
                ]


explodeImage4 :: SpriteImage
explodeImage4 = [ ((-2,-2), '\\'), ((0,-2), '|'), ((2,-2), '/'),
                  ((-2, 0), '-'), ((2,0), '-'),
                  ((-2,2), '/'), ((0,2), '|'), ((2,2), '\\')
                ]


spriteY :: Sprite -> Int
spriteY (Sprite (_,sy) _ _ _ _ _ _ _ _)
   = sy

spriteX :: Sprite -> Int
spriteX (Sprite (sx,_) _ _ _ _ _ _ _ _)
   = sx

spriteXY :: Sprite -> Coordinate 
spriteXY (Sprite (sx,sy) _ _ _ _ _ _ _ _)
   = (sx,sy)

spriteGunXY :: Sprite -> Coordinate 
spriteGunXY (Sprite (sx,sy) (gx,gy) _ _ _ _ _ _ _)
   = (sx+gx,sy+gy)

moveSprite :: Coordinate -> Sprite -> Sprite
moveSprite (dx, dy) (Sprite (sx,sy) gunOffset images imageIndex maxImIndex vis mSeq mInd maxInd)
   = Sprite (sx + dx, sy + dy) gunOffset images imageIndex maxImIndex vis mSeq mInd maxInd

newGunBullet :: Coordinate -> Sprite
newGunBullet (x,y) 
   = Sprite (x,y) (0,0) [gunBulletImage] 0 0 True [] 0 0

newInvBullet :: Coordinate -> Sprite
newInvBullet (x,y) 
   = Sprite (x,y) (0,0) [invBulletImage] 0 0 True [] 0 0

newInvader :: Coordinate -> Sprite

newInvader (x,y)
   = Sprite (x,y) (0,0) [invaderImage1, invaderImage2] 0 1 True invaderMotion 0 9

spriteGunX :: Sprite -> Int
spriteGunX (Sprite (sx,_) (dx,_) _ _ _ _ _ _ _)
   = sx + dx

spriteGunY :: Sprite -> Int
spriteGunY (Sprite (_,sy) (_,dy) _ _ _ _ _ _ _)
   = sy + dy

-- the second part of the tuple is the lifespan of the explosion

newExplosion :: Coordinate -> Sprite 
newExplosion (x,y)
   = Sprite (x,y) (0,0) [explodeImage1, explodeImage2, explodeImage3, explodeImage4] 0 3 True [] 0 0 


isEmpty [] = True
isEmpty _ = False
