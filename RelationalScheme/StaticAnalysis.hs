{- |
Module      :  $Header$
Description :  static analysis for Relational Schemes
Copyright   :  Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see Hets/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

static analysis for Relational Schemes
-}

module RelationalScheme.StaticAnalysis 
    (
        basic_Rel_analysis
    )
    where

import RelationalScheme.AS
import RelationalScheme.Sign
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Result
import Common.AS_Annotation
import qualified Data.Set as Set
import Common.Id
import Control.Monad            
import Data.Maybe            
            
basic_Rel_analysis :: (RSScheme, Sign,GlobalAnnos) ->
                      Result (RSScheme, ExtSign Sign RSSymbol,[Named Sentence])
basic_Rel_analysis (spec, sign, _) =
    let
        sens = getRels spec
        sig  = getSignature spec
    in
    do
        os <- sig `uniteSig` sign
        when (tables os == Set.empty) (fatal_error "Empty signature" nullRange)
        --look4keys sig
        mapM (analyse_relationship os) sens
        return  (spec, ExtSign
                    {
                        plainSign = os
                    ,   nonImportedSymbols = getSymbols sig
                    },
                    map makeNamedSen sens)

-- ^ Function to determine the symbols of a spec
getSymbols :: RSTables -> Set.Set RSSymbol
getSymbols inTbl =    
        Set.fold (\x y -> 
             Set.union 
                (foldl (\b a -> SColumn (t_name x) (c_name a) (c_data a) (c_key a)
                        `Set.insert` b) Set.empty $ columns x) $ 
                (STable $ t_name x) `Set.insert` y) Set.empty $ tables inTbl             

{-
-- ^ function to check if a key is defined for a table                
look4keys :: RSTables -> Result [RSTable]
look4keys rt =
        mapM (\x -> if ((Set.size $ t_keys x) >= 1) 
                    then
                        return x
                    else
                        fatal_error ("No key defined for : " ++ 
                            (show x)) (posOfId $ t_name x)
              ) $ Set.toList $ tables rt
-}

analyse_relationship :: RSTables -> Annoted RSRel -> Result (Annoted RSRel)
analyse_relationship tbi reli = 
    let
        tb  = tables tbi
        rel = item reli
        (relDom, relCo, _, rn) = case rel of 
            RSRel r1 r2 r3 r4 -> (r1,r2,r3,r4)
        (t2,_) = case head $ relCo of 
            RSQualId i1 i2 _ -> (i1, i2)
        tf2 = Set.toList $ Set.filter (\x -> t_name x == t2) tb
        keyz2 = t_keys $ head $ tf2
    in
        do
            mapM (analyse_RSQualid rn tb) relDom
            k2 <- mapM (analyse_RSQualidK rn tb) relCo
            let kl2 = Set.fromList $ map fromJust $ filter (\x -> case x of 
                                 Nothing -> False
                                 _       -> True) $map (\(_,y) -> y) k2   
            when (kl2 /= keyz2) (fatal_error ("Not all keys are used on the right hand side of: " ++
                (show rel)) rn)                                                
            return $ reli

analyse_RSQualid :: Range -> Set.Set RSTable -> RSQualId -> Result RSQualId
analyse_RSQualid rn st quid = 
    let
        (tname, cname) = case quid of 
            RSQualId i1 i2 _ -> (i1, i2)
        ft = Set.filter (\x -> t_name x == tname) st
        cols = Set.fromList $ map c_name $ columns $ head $ Set.toList ft
    in
      do
        when (cname `Set.notMember` cols) (fatal_error ((show cname) ++ " is not" ++
              " defined") rn)
        return $ quid

analyse_RSQualidK :: Range -> Set.Set RSTable -> RSQualId -> Result (RSQualId, Maybe Id)
analyse_RSQualidK rn st quid = 
    let
        (tname, cname) = case quid of 
            RSQualId i1 i2 _ -> (i1, i2)
        ft = Set.filter (\x -> t_name x == tname) st
    in
            case (Set.size ft) of
            0 -> return $ (quid, Nothing)
            1 -> do 
                        let tid  = head $ Set.toList ft
                            keyz = t_keys tid
                        when (cname `Set.notMember` keyz) (fatal_error ((show cname) ++ " is used "++ 
                                "as a key, but not defined as one") rn)
                        return $ (quid, Just $ cname)
            _ -> fatal_error ("Duplicate table name: " ++ (show ft)) rn
            