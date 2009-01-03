{- |
Module      :  $Header$
Description :  analyse annotations and add them to global ones
Copyright   :  (c) Christian Maeder, Klaus Luettich and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Some functions for building and accessing the datastructures of
 GlobalAnnotations
-}

module Common.AnalyseAnnos (addGlobalAnnos, store_literal_map) where

import Common.AS_Annotation
import Common.DocUtils
import Common.GlobalAnnotations
import Common.Id
import Common.Lexer (bind)
import Common.Result
import qualified Common.Lib.Rel as Rel

import qualified Data.Map as Map
import Data.List (partition)
import Control.Monad (foldM)
import Text.ParserCombinators.Parsec

-- | add global annotations
addGlobalAnnos :: GlobalAnnos -> [Annotation] -> Result GlobalAnnos
addGlobalAnnos ga all_annos = do
    do let (annos, rest_annos) = partition ( \ a -> case a of
            Label _ _ -> False
            Semantic_anno _ _ -> False
            Unparsed_anno _ _ _ -> False
            -- line and group and comments will be ignored
            _ -> True) all_annos
           ds = map ( \ d -> mkDiag Hint "no analysis of" d)
                rest_annos
       Result ds (Just ())
       n_prec_annos <- store_prec_annos (prec_annos  ga) annos
       n_assoc_annos <- store_assoc_annos (assoc_annos ga) annos
       n_display_annos <- store_display_annos (display_annos ga) annos
       n_literal_annos <- store_literal_annos (literal_annos ga) annos
       n_literal_map <- store_literal_map (literal_map ga) annos
       return ga { prec_annos = n_prec_annos
                 , assoc_annos = n_assoc_annos
                 , display_annos = n_display_annos
                 , literal_annos = n_literal_annos
                 , literal_map = n_literal_map}

-- | add precedences
store_prec_annos :: PrecedenceGraph -> [Annotation] -> Result PrecedenceGraph
store_prec_annos pgr ans =
  let showRel = showSepList (showString "\n") showIdPair . Rel.toList in
    fmap Rel.transClosure $
    foldM ( \ p0 an -> case an of
            Prec_anno prc lIds hIds _ ->
                 foldM (\ p1 li ->
                     foldM ( \ p2 hi -> -- hi und pi2 getauscht
                             if li == hi
                             then Result [mkDiag Error
                                       "prec_anno with equal id" hi] (Just p2)
                             else case prc of
                                    Lower -> if Rel.path hi li p2
                                             then Result [mkDiag Error
                                                        ("prec_anno conflict: "
                                                         ++ showId li " < "
                                                         ++ showId hi "\n"
                                                         ++ showRel p2 "") hi]
                                                           (Just p2)
                                             else return (Rel.insert li hi p2)
                                    BothDirections ->
                                             if Rel.path hi li p2 ==
                                                Rel.path li hi p2
                                             then return (Rel.insert hi li
                                                         (Rel.insert li hi p2))
                                             else Result [mkDiag Error
                                                        ("prec_anno conflict: "
                                                          ++ showId li " <> "
                                                          ++ showId hi "\n"
                                                          ++ showRel p2 "") hi]
                                                           (Just p2)
                                    _ -> Result [mkDiag Error
                                                 "prec_anno relation" hi]
                                                (Just p2)
                             ) p1 hIds
                       ) p0 lIds
            _ -> return p0) pgr ans

-- | add associative ids
store_assoc_annos :: AssocMap ->  [Annotation] -> Result AssocMap
store_assoc_annos
    = foldM ( \ am0 an ->
              case an of
              Assoc_anno as is _ ->
                foldM ( \ am1 i ->
                        let v = Map.lookup i am1 in
                        case v of
                        Nothing -> return $ Map.insert i as am1
                        Just os -> Result [if as == os then mkDiag Hint
                                "repeated associative identifier" i
                                                       else mkDiag Error
                                "identifier has already other associativity" i]
                                $ Just am1 ) am0 is
              _ -> return am0 )

-- | add display annotations
store_display_annos :: DisplayMap -> [Annotation] -> Result DisplayMap
store_display_annos =
    foldM ( \ m an ->
            case an of
            Display_anno i sxs _ ->
               do let t = Map.findWithDefault Map.empty i m
                  dm <- foldM ( \ table (df, str) ->
                        let oldTok = Map.findWithDefault tok df table
                            rtok = parse_display_str an str
                            tok = maybe [] id (maybeResult rtok)
                            checkToks toks id'@(Id toks' _ _) =
                                if c_plc toks == c_plc toks'
                                then []
                                else [mkDiag Error
                                        ("Number of places in identifier \""
                                         ++ showDoc id'
                                            (" \" does not meet number "++
                                             "of places in display string \""
                                             ++str ++"\"")) an]
                                where c_plc = foldl placePlus1 (0::Int)
                                      placePlus1 acc toky =
                                         if isPlace toky then acc+1 else acc
                        in
                        if oldTok == tok
                        then Result (diags rtok ++ checkToks tok i)
                                 $ Just $ Map.insert df tok table
                        else Result (diags rtok++[mkDiag Error ("conflict: "
                                     ++ showDoc an "") an]) $ Just table
                              ) t sxs
                  return $ Map.insert i dm m
            _ -> return m )

-- | add literal annotation to 'LiteralMap'
-- and check for overlapping ids
store_literal_map :: LiteralMap -> [Annotation] -> Result LiteralMap
store_literal_map =
    foldM ( \ m a ->
            case a of
            Number_anno id1 _ ->
                let oc = Map.findWithDefault Number id1 m in
                if oc == Number -- repeated or new
                then return $ Map.insert id1 Number m
                else Result [mkDiag Error
                               ("conflict: " ++ showDoc a "") id1] $ Just m
            String_anno id1 id2 _ ->
                let c = StringCons id1
                    oc = Map.findWithDefault c id2 m
                    on = Map.findWithDefault StringNull id1 m
                    in
                if oc == c && on == StringNull
                then return $ Map.insert id1 StringNull $ Map.insert id2 c m
                else Result [ mkDiag Error
                              ("conflict: " ++ showDoc a "") id1] $ Just m
            Float_anno id1 id2 _ ->
                let oc = Map.findWithDefault Fraction id1 m
                    on = Map.findWithDefault Floating id2 m
                    in
                if oc == Fraction && on == Floating
                then return $ Map.insert id2 Floating
                                   $ Map.insert id1 Fraction m
                else  Result [mkDiag Error
                              ("conflict: " ++ showDoc a "") id1] $ Just m
            List_anno id1 id2 id3 _ ->
                let c = ListCons id1 id2
                    n = ListNull id1
                    oc = Map.findWithDefault c id3 m
                    on = Map.findWithDefault n id2 m
                    in if c == oc && n == on
                    then return $ Map.insert id2 n $ Map.insert id3 c m
                    else  Result [mkDiag Error ("conflict: "
                                                ++ showDoc a "") id1]
                                         $ Just m
            _ -> return m )

-- | add literal annotation to 'LiteralAnnos'
-- and check for contradictions
store_literal_annos :: LiteralAnnos -> [Annotation] -> Result LiteralAnnos
store_literal_annos la ans =
    do n_string_lit <- setStringLit (string_lit la) ans
       n_list_lit <- setListLit (list_lit la) ans
       n_number_lit <- setNumberLit (number_lit la) ans
       n_float_lit <- setFloatLit (float_lit la) ans
       return la { string_lit = n_string_lit
                 , list_lit = n_list_lit
                 , number_lit = n_number_lit
                 , float_lit  = n_float_lit
                 }

-- | shortcut to show errors in 'setStringLit' and  'setFloatLit'
showIdPair :: (Id, Id) -> ShowS
showIdPair (i1, i2) = showId i1 . showString "," . showId i2

-- | add (and check for uniqueness) string annotations
setStringLit :: Maybe (Id,Id) -> [Annotation] -> Result (Maybe (Id,Id))
setStringLit =
    foldM ( \ m a ->
            case a of
            String_anno id1 id2 _ ->
                let q = (id1, id2) in
                case m of
                 Nothing -> return $ Just q
                 Just p ->
                     if q == p
                     then return m
                     else Result [mkDiag Error
                                 ("conflict %string " ++ showIdPair q
                                  " and " ++ showIdPair p "") id1] $ Just m
            _ -> return m )

-- | add (and check for uniqueness) floating annotations
setFloatLit :: Maybe (Id,Id) -> [Annotation] -> Result (Maybe (Id,Id))
setFloatLit =
    foldM ( \ m a ->
            case a of
            Float_anno id1 id2 _ ->
                let q = (id1, id2) in
                case m of
                Nothing -> return $ Just q
                Just p ->
                    if q == p
                    then return $ m
                    else  Result [mkDiag Error
                                 ("conflict %floating  " ++ showIdPair q
                                  " and " ++ showIdPair p "") id1] $ Just m
            _ -> return m )

-- | add (and check for uniqueness) number annotations
setNumberLit :: Maybe Id -> [Annotation] -> Result (Maybe Id)
setNumberLit =
    foldM ( \ m a ->
            case a of
            Number_anno id1 _ ->
                case m of
                Nothing -> return $ Just id1
                Just id2 ->
                    if id1 == id2 then return m
                    else Result [mkDiag Error
                                 ("conflict %number " ++ showId id1 " and "
                                  ++ showId id2 "") id1] $ Just m
            _ -> return m )

-- | add (and check for consistency) (possibly several) list annotations
setListLit :: Map.Map Id (Id,Id) -> [Annotation] -> Result (Map.Map Id (Id,Id))
setListLit =
    foldM ( \ m a ->
            case a of
            List_anno id1 id2 id3 _ ->
-- gleiche Keys mit verschiedenen Values sind ein Konflikt!!
                    let nv = (id2, id3)
                    in case Map.lookup id1 m of
                       Nothing -> return $ Map.insert id1 nv m
                       Just v  ->
                         if nv == v then return m
                         else Result [mkDiag Error
                                 ("conflict" ++ showListAnno id1 nv ++
                                  " and" ++ showListAnno id1 v) id1]
                                 $ Just m
            _ -> return m )
    where showListAnno i1 (i2, i3) = " %list " ++ showId i1 ","
                                ++ showId i2 "," ++ showId i3 ""

parse_display_str :: Annotation -> String -> Result [Token]
parse_display_str an str = case parse (tokenL [])
                                   "-- internal parse --"
                                   str of
                        Left err -> Result [mkDiag Warning
                                                   (err' ++show err++"\nin:\n")
                                                   an ]
                                           $ Just [Token str nullRange]
                        Right i' -> Result [] $ Just i'
    where tokenL acc =
              do isEof <- option False (eof >> return True)
                 if isEof
                    then return acc
                    else do plcs <- many $ try placeP
                            tok <- optTok $ nonPlaceP
                            if null tok
                               then return (acc ++ plcs)
                               else tokenL (acc ++ plcs ++tok)
          optTok pa = option [] (do t <- pa
                                    return [t])
          mkTok p = bind Token p (return nullRange)
          placeP = mkTok (string place)
          nonPlaceP = mkTok $
                         do c <- anyChar
                            cs <- manyTill anyChar (lookAhead (placeUn<|>eof))
                            return (c:cs)
              where placeUn = do try $ placeP
                                 return ()

          err' = "could not parse display string: using \""
                 ++ str ++ "\" as display token!\n"
