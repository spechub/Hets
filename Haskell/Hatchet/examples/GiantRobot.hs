-- GiantRobot.hs

-- An enormous haskell file with heaps of code

-- type sigs and synonyms have been commented out intentionally
-- so that full type inference is performed

------------------------------- AnsiScreen code

-- Basic screen control codes:


-- type Pos           = (Int,Int)

{-
at        :: Pos -> String -> String
highlight :: String -> String
goto      :: Int -> Int -> String
home      :: String
cls       :: String
-}

at (x,y) s  = goto x y ++ s
highlight s = ("\ESC[7m"++s)++"\ESC[0m"
goto x y    = '\ESC':('[':(show y ++(';':show x ++ "H")))
home        = goto 1 1

-- Choose whichever of the following lines is suitable for your system:
cls         = "\ESC[2J"     -- for PC with ANSI.SYS
--cls         = "\^L"         -- for Sun window


-----------------------------------------------------------------------------



--------------------------- Interact Code

--- Interactive program combining forms:

-- type Interact = String -> String

{-
end                      :: Interact
readChar, peekChar       :: Interact -> (Char -> Interact) -> Interact
pressAnyKey              :: Interact -> Interact
unreadChar               :: Char -> Interact -> Interact
writeChar                :: Char -> Interact -> Interact
writeStr                 :: String -> Interact -> Interact
ringBell                 :: Interact -> Interact
readLine                 :: String -> (String -> Interact) -> Interact
-}

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

       --rubout  :: Char -> Bool
       rubout c = (c=='\DEL') || (c=='\BS')

       --lineOut                      :: Int -> String -> String
       lineOut n ""                  = ""
       lineOut n (c:cs)
                 | n>0  && rubout c  = "\BS \BS" ++ lineOut (n-1) cs
                 | n==0 && rubout c  = lineOut 0 cs
                 | otherwise         = c:lineOut (n+1) cs

       -- noBackSpaces :: String -> String
       noBackSpaces  = reverse . delete 0 . reverse
                       where delete n ""          = ""
                             delete n (c:cs)
                                      | rubout c  = delete (n+1) cs
                                      | n>0       = delete (n-1) cs
                                      | otherwise = c:delete 0 cs

-----------------------------------------------------------------------------



------------------------------ AnsiInteract Code


-- Screen oriented input/output functions:

{-
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
-}

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


----------------------------------- Robot code

-------------------------------
-- Data and type definitions --
-------------------------------

-- Below you will find the essential data and type definitions of the robo project.
-- You will need to familiarize yourself with these definitions.


-- Positions of visible objects (such as robots and coins) are described by their
-- x- (first component) and y-coordinate (second component). Note that we use Integer's to 
-- represent positions rather than Integer.
-- We assume that the positive x-axis points to the east and the positive y-axis points
-- to the north

-- type Position = (Integer, Integer)      

-- Move describes the possible robo movement.

data Move = MvForward | MvLeft | MvRight | NoMv
             deriving (Eq, Show)


-- History contains a list of all previous moves plus the direct distance to the coin.
-- We assume that the most recent move performed  by the robot and the distance to the coin 
-- are stored as the item in the history list

-- type History = [(Move, Integer)]

-- A robot is identified by its current position 
-- (first component = x-position, second component = y-position)
-- on the field, the direction it's facing on the field (either west, east, south or north), and
-- a history of the previous moves plus distances to the coin

 

data Direction = West | East | South | North
                deriving (Eq, Show)

-- type Robot = (Position, Direction, History)


-- The current state of the roboworld is described by a pair consisting of
-- the description of the robot and the positon of the coin

-- type State = (Robot, Position)


-- The roboworld is divided into squares which are either
-- occupied by a robot, a coin (Cn), or an empty square (Bk).
-- We distinguish between robots either facing west (RbW), east (RbE), south (RbS) or north (RbN) 


data Square =  RbW | RbE | RbS | RbN | Bk | Cn 
               deriving (Eq, Show)




-- The robots vision is limited to the three squares on its left, front and right
-- with respect to the direction the robot is facing.
-- The sensor data is represented as a triple 
-- (first component= left, second component=front, third component=right)

-- type Sensor = (Square, Square, Square)


-- Below you will find some functions that allow you to play the robot game.
-- For the purpose of this project, it is not necessary for you to understand
-- the functionality of the functions below to successfully complete the project. 
-- However, you might be interested in understanding their purpose.


-----------------------
-- Output functions --
-----------------------


-- Note that the roboworld is unbound.
-- The current field of interest contains the area occupied by 
-- all visible objects (robots and coins)
-- The field of all visible objects is represented by a list of a list of squares.

-- type Field = [[Square]]


-- constructfield takes the current state of the world and constructs a field which is just big
-- enough to contain all visible objects
-- You need to compute the min (resp. max) position of the set of all visible objects
-- constructfield :: State -> Field
constructfield (((robox, roboy),d,_), (coinx, coiny)) = 
   let 
       robot (x,y) = (x == robox) && (y== roboy)
       dir West = RbW
       dir East = RbE
       dir South = RbS
       dir North = RbN
       cn (x,y) = (x == coinx) && (y == coiny)
       output (x,y) = if cn (x,y) 
                      then Cn
                      else if robot (x,y)
                           then dir d
                           else Bk  
       minx = min robox coinx
       maxx = max robox coinx
       miny = min roboy coiny
       maxy = max roboy coiny                               
   in [ [output(x,y) | x <- [minx..maxx] ] |  y <- [miny..maxy]]



-- The display function actually outputs the field on the screen
-- display :: Field -> IO ()
display [] = do putStr "\n"
                putStr "Continue (y/n) : "
                c <- getChar
                if c /= 'y' then error "You did abort the game" -- display []
                 else return ()
display (x:xs) = let displaychar RbW = putChar 'W'
                     displaychar RbE = putChar 'E'
                     displaychar RbS = putChar 'S'
                     displaychar RbN = putChar 'N'
                     displaychar Bk = putChar '_'
                     displaychar Cn = putChar '*'
                     display2 [] = return ()
                     display2 (y:ys) = do displaychar y
                                          display2 ys
                 in do display2 x
                       putStr "\n"
                       display xs


------------------
-- main routine --
------------------


-- runRobot is the main driving routine.
-- runRobot takes some of the functions you are meant to implement and 
-- an initial state and then starts searching for the coin
-- if the robot finds the coin, the robot goes into returnmode and tries
-- to get back to its initial position
runRobot position hitCoin sensor distanceToCoin updateHistory performMv seekCoin returnCoin state = 
 let initialrobopos = position state  -- initial position of the robot
     --seekmode :: State -> IO ()
     seekmode state = 
                 if not (hitCoin state)   -- remain in seek mode
                 then let sensordata = sensor state
                          dist = distanceToCoin state
                          (robot,_) = state
                          mv = seekCoin (robot, sensordata, dist)
                          newstate' = performMv mv state
                          newstate = updateHistory mv dist newstate'
                      in do display (constructfield newstate)
                            seekmode newstate
                 else returnmode state
     --returnmode :: State -> IO ()
     returnmode state =
               let (robot,_) = state
                   (pos,_,_) = robot
               in if pos == initialrobopos
                  then do putStr "Your robot did find the coin and returned home safely!"
                   else let sensordata = sensor state
                            mv = returnCoin (robot, sensordata)
                            newstate' = performMv mv state
                            newstate = updateHistory mv 0 newstate' -- the robot carries the coin now
                        in do display (constructfield newstate)            -- therefore we have a 0 distance
                              returnmode newstate
     in do display (constructfield state)
           seekmode state







------------------------------- RobotWorld code

-- the above module is supplied
-- please take a look at the data and type definitions in Robot.hs
-- you will need to understand their purposes
-- DO NOT make any changes in Robot.hs


-- Your task is to implement some functions which will allow you to play the robot game.
-- Full type signatures are provided for all functions which you have to implement.
-- DO NOT change any function names and type signatures.
-- However, you need to provide the function body and may add subsidiary functions.
-- At the moment, all function bodies contain  error "Your code".
-- The functions which you have to implement are divided into three groups.

-----------------------------------
-- Robot access/update functions --
-----------------------------------

-- direction :: State -> Direction
direction state = dir
    where  (rb,cpos) = state
           (_,dir,_) = rb

-- position :: State -> Position
position state = pos
    where  (rb,cpos) = state
           (pos,_,_) = rb

-- history :: State -> History
history state = his
    where  (rb,cpos) = state
           (_,_,his) = rb

-- updateHistory :: Move -> Integer -> State -> State
updateHistory mv d state = ((pos,dir,his++[(mv,d)]),cpos)
    where  (rb,cpos) = state
           (pos,dir,his) = rb


-------------------------
-- Robot movements/etc --
-------------------------

-- distanceToCoin :: State -> Integer
distanceToCoin state = round (sqrt (fromIntegral (xd^2 + yd^2)))
    where  (rb,(cx,cy)) = state
           ((rx,ry),dir,his) = rb
           xd = rx - cx
           yd = ry - cy


-- hitCoin :: State -> Bool
hitCoin state = rpos == cpos
    where  (rb,cpos) = state
           (rpos,_,_) = rb

-- mvRobotForward :: State -> State
mvRobotForward state = (((nx,ny),dir,his),cpos)
    where  (rb,cpos) = state
           ((rx,ry),dir,his) = rb
           (nx,ny) = newXY dir
           newXY West = (rx-1,ry)
           newXY East = (rx+1,ry)
           newXY South = (rx,ry-1) 
           newXY North = (rx,ry+1) 
{-
           (nx,ny) | dir == West = (rx-1,ry)
                   | dir == East = (rx+1,ry)
                   | dir == South = (rx,ry-1)
                   | dir == North = (rx,ry+1)
-}

-- turnRobotLeft :: State -> State
turnRobotLeft state = ((rpos,ndir dir,his),cpos)
    where  (rb,cpos) = state
           (rpos,dir,his) = rb
           ndir West = South
           ndir East = North
           ndir South = East
           ndir North = West

-- turnRobotRight :: State -> State
turnRobotRight state = ((rpos,ndir dir,his),cpos)
    where  (rb,cpos) = state
           (rpos,dir,his) = rb
           ndir West = North
           ndir East = South
           ndir South = West
           ndir North = East

-- performMv           :: Move -> State -> State
performMv MvForward = mvRobotForward
performMv MvLeft    = turnRobotLeft
performMv MvRight   = turnRobotRight
performMv NoMv      = id

-- sensor :: State -> Sensor
sensor state = (contents l,
                contents f,
                contents r)
    where  (rb,cpos) = state
           ((rx,ry),dir,his) = rb
           (l,f,r) = lfr dir
           lfr West = ((rx-1,ry-1),(rx-1,ry),(rx-1,ry+1))
           lfr East = ((rx+1,ry+1),(rx+1,ry),(rx+1,ry-1))
           lfr South = ((rx+1,ry-1),(rx,ry-1),(rx-1,ry-1))
           lfr North = ((rx-1,ry+1),(rx,ry+1),(rx+1,ry+1))

           contents s | s == cpos = Cn



------------------------
-- tactical functions --
------------------------


{-

seekCoin :: (Robot, Sensor, Int) -> Move
seekCoin (rb, s, d) = error "Your code"

returnCoin :: (Robot, Sensor) -> Move
returnCoin (rb, s) = error "Your code"

-}


-----------------------
-- Sample input data --
-----------------------


-- Below you will find some sample data which allows you to play the robot game,
-- if you have successfully implemented all of the functions above


-- emptyHistory :: History
emptyHistory = [(NoMv,17)] -- 17 is the distance from the robot to the coin
                           -- in case of the given sample state

samplestate = (((1 , 1 ), West, emptyHistory), (15 , 11 ))


-- The function runRobot is defined in Robot.hs. You do not need to understand its functionality.
-- runRobot takes the function position, hitCoin, sensor, distancetoCoin, performMv, seekCoin,
-- returnCoin and an initial state as an argument and starts searching for a coin.
-- If the robot finds a coin (this depends on how good your seekCoin function is),
-- the robot tries to get back to its original position (this depends on how good your returnCoin
-- function is)
-- All you need to do is to type in run in Hugs
-- You can simply adjust the positon of the coin and the robot by changing the
-- emptyHistory and samplestate definitions above

-- run = runRobot position hitCoin sensor distanceToCoin updateHistory performMv seekCoin returnCoin samplestate





-- yeah, yeah.  I know this could be made much nicer,  but cut 'n' paste does the job
-- it returns the lengths of the previous three runs.
-- immHistory :: Bool -> History -> (Integer, Integer, Integer)
immHistory ret xs = help1 (0,0,0) xs
    where
    help1 acc []                         = acc
    help1 acc ((_,d):_) | (d > 0) && ret = acc
    help1 (j,0,0) ((MvForward,_):mvs)    = help1 (j+1,0,0) mvs
    help1 (j,0,0) (_:mvs)                = help2 (j,0,0) mvs

    help2 acc []                         = acc
    help2 acc ((_,d):_) | (d > 0) && ret = acc
    help2 (j,k,0) ((MvForward,_):mvs)    = help2 (j,k+1,0) mvs
    help2 (j,k,0) (_:mvs)                = help3 (j,k,0) mvs

    help3 acc ((_,d):_) | (d > 0) && ret = acc
    help3 (j,k,l) ((MvForward,_):mvs)    = help3 (j,k,l+1) mvs
    help3 acc _                          = acc



-- We just spiral.  If we have moved less than the previous run we go forward
-- If we are equal to the last run,  but that was equal to its previous run we also
-- go forward.  Else turn right!
-- makeMove :: Bool -> History -> Move
makeMove ret mvs
    | (j < k) || ((j == k) && (k == l)) = MvForward
    | otherwise = MvRight
    where (j,k,l) = immHistory ret mvs



-- Kevin's solution





-- seekCoin :: (Robot, Sensor, Integer) -> Move
seekCoin (rb, s, d) = makeMove False $ reverse mvs
    where (_,_,mvs) = rb







-- returnCoin :: (Robot, Sensor) -> Move
returnCoin (rb, s) = makeMove True $ reverse mvs
    where (_,_,mvs) = rb







{-
seekCoin :: (Robot, Sensor, Integer) -> Move


-- empty history
seekCoin ((_, _, []), _, d) = MvRight

-- non-empty history
seekCoin ((_, _, history), _, d)
   | previousMove == MvRight = MvForward
   | otherwise = if previousDistance <= d then MvRight else MvForward
   where
   previousMove = fst (last history)
   previousDistance = snd (last history)

-}








{-
-- bernie's second solution
seekCoin ((_, _, []), _, d) = MvRight


seekCoin ((_, _, history), _, d)
   | previousMove == MvRight = MvForward
   | last3Dists == [2,3,3] = MvRight
   | otherwise = if previousDistance < d then MvRight else MvForward
   where
   previousMove = fst (last history)
   previousDistance = snd (last history)
   last3Dists = map snd (take 3 (reverse history))
-}


{-


-- bernie's solution
returnCoin :: (Robot, Sensor) -> Move

returnCoin ((_, _, history), _)
   | firstOrSndMove = MvRight
   | thirdMove = MvForward
   | otherwise = invertMv $ head $ drop (((distFromZero - 3) * 2) + 4) histMoves 
   where
   histMoves = map fst $ reverse history
   firstOrSndMove = numZeroDists <= 1
   thirdMove = numZeroDists == 2
   numZeroDists = length [d | (m,d) <- history, d == 0]
   distFromZero = length $ dropWhile (/= 0) $ map snd $ history



invertMv :: Move -> Move
invertMv MvLeft = MvRight
invertMv MvRight = MvLeft
invertMv x = x


-}

--------------------------- AnimateRobot code


{-------------------------------------------------------------------------------

        module:         AnimateRobot (version 2)

        note:           This version of the code contains an initial history
                        which contains a single NoMv. The previous version
                        of the code contained an initial history that
                        was completely empty (ie the empty list []). 

        author:         Bernie Pope

        description:    This module contains some Haskell code for 
                        animating the robot from the 433-141 project
                        semester 2 2000, on an ANSI terminal.

                        It must be used in conjunction with the modules:                                
                        Robot and RobotWorld. In particular it requires that
                        the functions seekCoin and returnCoin are implemented.

                        It also requires the library module AnsiInteract which
                        is provided with all modern versions of hugs.

                        It draws the progress of the robot as it seeks for the
                        coin and as it returns to its original position. The
                        grid displayed is limited to 25 rows and 80 columns:
                        you must make sure your terminal is at least this large
                        for the animation to work correctly (most terminals
                        start with these dimensions, for example xterm on
                        unix machines).

                        The origin of the grid is in the bottom left corner of
                        the display. The y axis (North) is in the positive row
                        direction, and the x axis (East) is in the positive
                        column direction (ie North is upwards and East is 
                        rightwards).

                        The bottom left corner has coordinates (1,1), the
                        top right corner has coordinates (80,25) - note
                        that coordinates are specified in (x,y) orientation.

                        If either of the robot or coin are outside of the
                        25x80 viewing grid then they will not be displayed. 
                        Note that the robot may traverse outside of the 
                        viewing grid temporarily. Display of the robot will
                        continue if it enters the viewing grid again.

        usage:         animate speed rob_pos rob_dir coin_pos

                        speed::Int 
                           controls the speed of the animation. On most 
                           machines a number in the range 0-20 should suffice, 
                           0 = fastest.

                        rob_pos::Position
                           the initial position of the robot

                        rob_dir::Direction
                           the initial direction that the robot is facing 

                        coin_pos::Position
                           the initial position of the coin 

                        example:
                        animate 15 (30,15) West (25,10)

                        If you wish to terminate the animation press
                        control-C simultaneously - this will return you to
                        the hugs prompt.

        platforms:      This code will work on a unix machine with xterm (ie
                        all unix machines at Melbourne University). The code
                        will also work on Windows machines which support
                        ANSI terminals - this may be difficult to set up. 

        notes:          You should not have to modify your code or the code
                        provided to you in any way to make use of this module.
                        You should not submit this module or any part of it.
                        The module is provided as a tool to visualize your
                        seekCoin and returnCoin functions. You are free to
                        modify this code and re-distribute it in any way that
                        you desire. 

-------------------------------------------------------------------------------}



-- animate :: Integer -> Position -> Direction -> Position -> IO ()



animate s (rx,ry) rdir (cx,cy) 
  = runRobot' s position hitCoin sensor distanceToCoin updateHistory performMv seekCoin returnCoin initState 
  where
  initState = (((rx, ry), rdir, [(NoMv, distToCoin)]), (cx, cy))
  distToCoin = round (sqrt (fromIntegral  (xd^2 + yd^2)))
  xd = rx - cx
  yd = ry - cy

main = animate 15 (30,15) West (25,10)  

data Mode = Seek | Return
            deriving Eq 


runRobot' speed position hitCoin sensor distanceToCoin updateHistory performMv seekCoin returnCoin state =
 let initialrobopos = position state  -- initial position of the robot

     -- seekmode :: State -> Interact -> Interact
     seekmode state i =
                 if not (hitCoin state)   -- remain in seek mode
                 then let sensordata = sensor state
                          dist = distanceToCoin state
                          (robot,_) = state
                          mv = seekCoin (robot, sensordata, dist)
                          newstate' = performMv mv state
                          newstate = updateHistory mv dist newstate'
                      in  (displayAnsi (Just mv) speed Seek initialrobopos newstate (seekmode newstate i))
                 else returnmode state i

     -- returnmode :: State -> Interact -> Interact
     returnmode state i =
               let (robot,_) = state
                   (pos,_,_) = robot
               in if pos == initialrobopos
                  then i 
                  else let sensordata = sensor state
                           mv = returnCoin (robot, sensordata)
                           newstate' = performMv mv state
                           newstate = updateHistory mv 0 newstate' -- the robot carries the coin now
                        in (displayAnsi (Just mv) speed Return initialrobopos newstate (returnmode newstate i))


     in runI ( clearScreen ( initGrid state ( displayAnsi Nothing speed Seek initialrobopos state (seekmode state ( moveTo (1,1) end))))) 

--runI :: Interact -> IO ()
runI i = putStr $ i ""


--displayAnsi :: Maybe Move -> Integer -> Mode -> Position -> State -> Interact -> Interact
displayAnsi move speed mode (ix, iy) (((robx, roby), dir, _), (coinx, coiny)) i
   | isSeek mode = writeMode ("Seek" ++ showMove move) "%"
   | otherwise = writeMode ("Return" ++ showMove move) "*"
   where
   isSeek Seek = True
   isSeek _ = False
   writeMode s c = safeWriteAt robPos c ( safeWriteAt (1,1) s ( safeWriteAt initPos "_" (moveTo initPos' (pause speed i))))
   robPos = (robx, 25 - (roby - 1))
   initPos = (ix, 25 - (iy - 1))
   initPos' = (fromIntegral ix, fromIntegral $ 25 - (iy - 1))


-- safeWriteAt :: Position -> String -> Interact -> Interact 
safeWriteAt (x,y) s i
   | or [x < 1, x > 80, y < 1, y > 25] = i 
   | otherwise = (writeAt (fromIntegral x, fromIntegral y) s) i

-- initGrid :: State -> Interact -> Interact
initGrid (((robx, roby), dir, _), (coinx, coiny))
   = interactList [safeWriteAt (robx, 25 - (roby - 1)) "_" , safeWriteAt (coinx, 25 - (coiny - 1)) "C"]

-- showMove :: Maybe Move -> String
showMove Nothing = ""
showMove (Just MvForward) = (" MvForward") ++ "     "
showMove (Just MvLeft) = (" MvLeft") ++ "     "
showMove (Just MvRight) = (" MvRight") ++ "     "
showMove (Just NoMv) = (" NoMv") ++ "     "


--interactList :: [Interact -> Interact] -> Interact -> Interact
interactList xs i = foldr id i xs

-- yeah, I know this is a hack.

-- pause :: Integer -> Interact -> Interact
pause speed i 
   | speed < 0 = error "The speed value must be non-negative"
   | otherwise = seq (fib speed) i 

-- fib :: Integer -> Integer
fib 0 = 1
fib 1 = 1
fib n = (fib (n-1)) + (fib (n-2))



