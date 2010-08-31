{- |
Module      :  $Header$
Description :  Export of the MPTP.Profile table to KRHyper format
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.DB.Export where

import Config (home,dbDriver,dbServer,dbDatabase,dbPassword,dbUsername)
import qualified Utils.SetMap as SM
import Data.List
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Char (toUpper)
import Database.HaskellDB
import Database.HaskellDB.GenericConnect
import Database.HaskellDB.HDBRec
import Search.DB.Connection
import Search.DB.MPTP.Profile hiding (Skeleton)
import System.IO
--import Control.Monad (filterM)

data Sequent = 
    Seq {assumptions :: [AbstractFormula],
         conclusion :: AbstractFormula} deriving (Show)
type AbstractFormula = (String,[String])

exportToKrhyper =
    do md5s <- getField skeleton_md5
       filenames <- getField file
       writeAxiomFiles md5s filenames
       mapM (writeRuleFile md5s filenames) (getGroups filenames)
       return 0


writeRuleFile md5s filenames group =
    do seqs <- getSequents md5s filenames group
       writeSequents group seqs
{-      
writeRuleFile "aff_2"
-}

dfg_krh = home ++ "/dfg/krh/"

writeSequents group seqs =
    do outhandle <- openFile (dfg_krh ++ "rules/" ++ group) AppendMode
       hPutStrLn outhandle ("% " ++ group ++ "\n\n")
       hPutStrLn outhandle $ formatSequents seqs
       hFlush outhandle

writeAxiomFiles md5s filenames =
    do filesAndSeqs <- mapM (getSequent md5s) filenames
       mapM writeAxioms filesAndSeqs
       return "habe fertig"

writeAxioms (file,seq) =
    do outhandle <- openFile (dfg_krh ++ "axioms/" ++ file ++ ".axioms") AppendMode
       putStrLn file
       hPutStrLn outhandle $ formatAxioms (file,seq)
       hFlush outhandle


formatSequents seqs = concat $ intersperse "\n\n" (map formatSequent seqs)
formatSequent (file,Seq assumptions conclusion) =  "% " ++ file ++ "\n" ++   (formatAbstractFormula conclusion)    ++ ":-\n\t" ++ (concat $ intersperse ",\n\t" $ map formatAbstractFormula assumptions) ++ "."
formatAbstractFormula (h,args) = h ++ "(" ++ (concat $ intersperse "," (map upperFirst args)) ++ ")"
formatAxioms (file,Seq assumptions _) = "% " ++ file ++ "\n" ++ (concat $ map formatAxiom assumptions)
formatAxiom  (h,args) = h ++ "(" ++ (concat $ intersperse "," args) ++ ").\n"
upperFirst (c:str) = (toUpper c):str
{-
*DB.Export> hr <- hide $ getField skeleton_md5
habe fertig
*DB.Export> let (Hide md5s) = hr
*DB.Export> hr <- hide $ getField file
habe fertig
*DB.Export> let (Hide filenames) = hr

*DB.Export> seqs <- getSequents md5s filenames "zfmisc_1"
[("zfmisc_1__t100_zfmisc_1.dfg",Seq [("H1892",["r2_hidden","r2_hidden"]),("H8944",["k1_zfmisc_1","r2_hidden","r1_tarski","k1_zfmisc_1","r1_tarski","r2_hidden","r2_hidden","r1_tarski","k1_zfmisc_1","r2_hidden","k1_zfmisc_1","r2_hidden","r1_tarski","k1_zfmisc_1","r1_tarski","k1_zfmisc_1","r2_hidden","r1_tarski"]),("H6020",["r2_hidden","r1_tarski","r2_hidden","r1_tarski","r2_hidden","r2_hidden","r1_tarski"]),("H12556",[]),("H6737",["r2_hidden","r1_tarski","k3_tarski"]),("H6857",["v1_xboole_0"]),("H10165",["v1_xboole_0"]),("H10273",["r1_tarski"])] ("H16215",["r1_tarski","k1_zfmisc_1","k3_tarski"])),("zfmisc_1__t101_zfmisc_1.dfg",Seq [("H1892",["r2_hidden","r2_hidden"]),("H15818",["k2_xboole_0","k2_xboole_0"]),("H15818",["k3_xboole_0","k3_xboole_0"]),("H5272",["r1_tarski","r1_tarski","r1_tarski","r1_tarski"]),("H13679",["r2_hidden","r2_hidden","k2_xboole_0","r2_hidden","r2_hidden","k2_xboole_0","r2_hidden","r2_hidden","r2_hidden","k2_xboole_0","r2_hidden","r2_hidden","r2_hidden","k2_xboole_0","r2_hidden","r2_hidden","k2_xboole_0","r2_hidden","r2_hidden","r2_hidden","k2_xboole_0","r2_hidden","r2_hidden","k2_xboole_0","r2_hidden","r2_hidden","r2_hidden","k2_xboole_0","r2_hidden","r2_hidden","k2_xboole_0"]),("H6020",["r2_hidden","r1_tarski","r2_hidden","r1_tarski","r2_hidden","r2_hidden","r1_tarski"]),("H12879",["r2_hidden","r2_hidden","k3_xboole_0","r2_hidden","r2_hidden","k3_xboole_0","r2_hidden","r2_hidden","r2_hidden","k3_xboole_0","r2_hidden","r2_hidden","k3_xboole_0","r2_hidden","r2_hidden","k3_xboole_0","r2_hidden","r2_hidden","k3_xboole_0","r2_hidden","r2_hidden","r2_hidden","k3_xboole_0","r2_hidden","r2_hidden","r2_hidden","k3_xboole_0","r2_hidden","r2_hidden","r2_hidden","k3_xboole_0"]),("H14488",["k3_tarski","r2_hidden","r2_hidden","r2_hidden","r2_hidden","r2_hidden","r2_hidden","r2_hidden","r2_hidden","r2_hidden","r2_hidden","r2_hidden","r2_hidden","k3_tarski"]),("H12556",[]),("H16237",["v1_xboole_0","v1_xboole_0","k2_xboole_0"]),("H2906",["v1_xboole_0","v1_xboole_0","k2_xboole_0"]),("H11863",["k2_xboole_0"]),("H11863",["k3_xboole_0"]),("H6857",["v1_xboole_0"]),("H10165",["v1_xboole_0"]),("H10273",["r1_tarski"]),("H12766",["r1_xboole_0","r1_xboole_0"]),("H12745",["r1_xboole_0","r2_hidden","k3_xboole_0","r1_xboole_0","r2_hidden","k3_xboole_0"]),("H4663",["r1_tarski","k3_tarski","k3_xboole_0","k3_xboole_0","k3_tarski","k3_tarski"])] ("H9439",["k3_tarski","k3_xboole_0","k3_xboole_0","k3_tarski","k3_tarski","r1_xboole_0","k3_tarski","k3_xboole_0","k3_xboole_0","k3_tarski","k3_tarski","k3_tarski","k3_xboole_0","k3_xboole_0","k3_tarski","k3_tarski","r2_hidden","k2_xboole_0","k3_tarski","k3_xboole_0","k3_xboole_0","k3_tarski","k3_tarski","r2_hidden","k2_xboole_0"]))]

-}


getSequents md5s filenames group =
    let theories = groupFileNames filenames
        (Just fileNameSet) = M.lookup group theories
        fileNameList = S.toList fileNameSet
    in do mapM (getSequent md5s) fileNameList --(take 2 fileNameList)

{-
        removeEmptyAssumptions seq = filter (not . null . snd) (assumptions $ snd seq)
    in do seqs <- mapM (getSequent md5s) (take 2 fileNameList)
          --return $ filter (not . null . assumptions . snd) seqs
          return $ map removeEmptyAssumptions seqs
-}        

getSequent md5s file =
    do abstractFormulas <- getAbstractFormulas file
       return (file,(tuplesToSequent md5s abstractFormulas))

tuplesToSequent md5s tuples = Seq assumptions conclusion
    where (axs,cs) = partition isAxiom tuples
          isAxiom tuple = fst tuple == "axiom"
          assumptions = map ((md5ToId md5s) . snd) axs
          conclusion = case cs of [(_,c)] -> md5ToId md5s c
                                  _ -> error "there is not exactly one conclusion"

md5ToId md5s (md5,ps) = case elemIndex md5 md5s
                        of (Just id) -> (('h':(show id)),ps)
                           Nothing -> error (md5 ++ " does not exist")

getAbstractFormulas file =
    do recs <- selectMd5Params file
       return (map recToTuple recs)

recToTuple rec = (role,(skeleton_md5,params))
    where (RecCons role (RecCons skeleton_md5 (RecCons paramStr _))) = rec RecNil
	  params = (read paramStr)::[String]

selectMd5Params f =
    do withDB $ do t <- table profile
		   restrict (t!file .==. (constant f) .&&.
                             t!skeleton .<>. (constant "true"))
		   project (role << t!role #
                            skeleton_md5 << t!skeleton_md5 #
			    parameter << t!parameter)

data Hide a = Hide a
instance Show (Hide a) where
    show a = "habe fertig"

hide a = a >>= return . Hide

groupFileNames names = SM.fromListSetValues $ map mkPair names
    where mkPair name = (getPrefix name,name)

getGroups names = S.toList $ fill names S.empty
    where fill (n:names)acc = fill names (S.insert (getPrefix n) acc)
          fill [] acc = acc

getPrefix str = concat $ takeWhile ("__"/=) $ group str

getFilesOf filenames pre = filter (\file -> (getPrefix file) == pre) filenames

{-
*DB.Export> groupFileNames names
fromList [("aff_1",fromList ["aff_1__t48_aff_1.dfg","aff_1__t49_aff_1.dfg","aff_1__t50_aff_1.dfg","aff_1__t51_aff_1.dfg"]),("alg_1",fromList ["alg_1__t7_alg_1.dfg","alg_1__t8_alg_1.dfg","alg_1__t9_alg_1.dfg"]),("algspec1",fromList ["algspec1__t10_algspec1.dfg","algspec1__t11_algspec1.dfg"])]
-}

names = ["aff_1__t48_aff_1.dfg",
         "aff_1__t49_aff_1.dfg",
         "aff_1__t50_aff_1.dfg",
         "aff_1__t51_aff_1.dfg",
         "alg_1__t7_alg_1.dfg",
         "alg_1__t8_alg_1.dfg",
         "alg_1__t9_alg_1.dfg",
         "algspec1__t10_algspec1.dfg",
         "algspec1__t11_algspec1.dfg"]
