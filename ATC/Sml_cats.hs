{- |
Module      :  $Header$
Description :  conversions to and from old SML aterm format
Copyright   :  (c) Klaus Lüttich and Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Grothendieck)

This module exports functions, that can convert an sml-CATS ATerm
   into the Haskell abstract syntax tree. So it contains all the
   necessary instances of ATermConvertible and a heuristic function
   that calculates the new lists of Pos out of Region tuples.

   the templates for the instances are automatically derived by
   DrIFT. But there were made many hand written changes.

   todo:
     - p_flag from pos-TERM is not considered jet!
-}


module ATC.Sml_cats ( ATermConvertibleSML
                    , from_sml_ATermString
                    , read_sml_ATerm
                    ) where

import Data.List (isPrefixOf)

import qualified Data.Map as Map
-- better recompilation checking without 'import Common.ATerm.Lib'
import Common.ATerm.AbstractSyntax
import Common.ATerm.ReadWrite

import Common.Id
import Common.AS_Annotation
import Common.LibName

import CASL.AS_Basic_CASL

import CASL.Logic_CASL
import Logic.Grothendieck

import Syntax.AS_Structured
import Syntax.AS_Architecture
import Syntax.AS_Library

-- the following module provides the ability to parse the "unparsed-anno"
import Text.ParserCombinators.Parsec (parse)
import qualified Common.Anno_Parser (annotations,parse_anno)
import Common.Lexer(skip)

-- |
-- like the chomp from Perl
-- but this chomp removes trailing newlines AND trailing spaces if any
chomp :: String -> String
chomp = reverse . chomp' . reverse
    where chomp' [] = []
          chomp' xs@(x:xs') | x == '\n' || x == ' ' = chomp' xs'
                            | otherwise = xs


read_sml_ATerm :: FilePath -> IO LIB_DEFN
read_sml_ATerm fn = readFile fn >>= return . from_sml_ATermString

----- Convertible class for sml -----------------------------------------

class ATermConvertibleSML t where
    from_sml_ShATerm     :: ATermTable -> t
    from_sml_ShATermList :: ATermTable -> [t]

    -- default function ignores the annotation part
    from_sml_ShATermList at =
        case aterm of
        ShAList ats _ ->  map cnvrt ats
        _           -> from_sml_ShATermError "[a]" aterm
        where aterm  = getATerm at
              cnvrt i = from_sml_ShATerm (getATermByIndex1 i at)

from_sml_ATermString :: ATermConvertibleSML a => String -> a
from_sml_ATermString s   = (\ a -> from_sml_ShATerm a) (readATerm s)

from_sml_ShATermError :: String -> ShATerm -> a
from_sml_ShATermError t u =
    error ("Cannot convert Sml-ShATerm to " ++ t ++ ": "++ err)
    where err = case u of
                  ShAAppl s l _ -> "!ShAAppl " ++ s ++ "("
                                   ++ show (length l) ++ ")"
                  ShAList _ _   -> "!ShAList"
                  _             -> "!ShAInt"

-- basic instances -----------------------------------------------
instance ATermConvertibleSML Bool where
    from_sml_ShATerm att = case at of
                       ShAAppl "true"  [] _ -> True
                       ShAAppl "false" [] _ -> False
                       _                     -> from_sml_ShATermError "Bool" at
                      where at = getATerm att
-- for Integer derive : ATermConvertibleSML hand written!

instance ATermConvertibleSML Integer where
    from_sml_ShATerm att = case getATerm att of
                           ShAInt x _ -> x
                           at  -> from_sml_ShATermError "Integer" at

instance ATermConvertibleSML Int where
    from_sml_ShATerm att = integer2Int $ from_sml_ShATerm att

instance ATermConvertibleSML Char where
   from_sml_ShATerm att = case at of
                      (ShAAppl s [] _) -> str2Char s
                      _                ->  from_sml_ShATermError "Char" at
                      where at = getATerm att
   from_sml_ShATermList att = case at of
                         (ShAAppl s [] _) -> read s
                         _                -> from_sml_ShATermError "String" at
                       where at = getATerm att

instance (Ord a, ATermConvertibleSML a, ATermConvertibleSML b)
    => ATermConvertibleSML (Map.Map a b) where
    from_sml_ShATerm att  = Map.fromList $ from_sml_ShATerm att

instance ATermConvertibleSML a => ATermConvertibleSML [a] where
    from_sml_ShATerm att  = from_sml_ShATermList att

instance (ATermConvertibleSML a,ATermConvertibleSML b)
    => ATermConvertibleSML (a,b) where
    from_sml_ShATerm att = case at of
                       (ShAAppl "" [x,y] _) -> (x',y')
                        where x' = from_sml_ShATerm (getATermByIndex1 x att)
                              y' = from_sml_ShATerm (getATermByIndex1 y att)
                       _  -> from_sml_ShATermError "(a,b)" at
                      where at = getATerm att

instance (ATermConvertibleSML a, ATermConvertibleSML b, ATermConvertibleSML c)
    => ATermConvertibleSML (a,b,c) where
    from_sml_ShATerm att = case at of
                       (ShAAppl "" [a,b,c] _) -> (a',b',c')
                         where a' = from_sml_ShATerm (getATermByIndex1 a att)
                               b' = from_sml_ShATerm (getATermByIndex1 b att)
                               c' = from_sml_ShATerm (getATermByIndex1 c att)

                       _   -> from_sml_ShATermError "(a,b,c)" at
                      where at = getATerm att

instance (ATermConvertibleSML a, ATermConvertibleSML b,
          ATermConvertibleSML c, ATermConvertibleSML d)
    => ATermConvertibleSML (a,b,c,d) where
    from_sml_ShATerm att = case at of
                       (ShAAppl "" [a,b,c,d] _) -> (a',b',c',d')
                         where a' = from_sml_ShATerm (getATermByIndex1 a att)
                               b' = from_sml_ShATerm (getATermByIndex1 b att)
                               c' = from_sml_ShATerm (getATermByIndex1 c att)
                               d' = from_sml_ShATerm (getATermByIndex1 d att)
                       _ -> from_sml_ShATermError "(a,b,c)" at
                      where at = getATerm att

----- instances of Id.hs ------------------------------------------------
instance ATermConvertibleSML Token where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "token" [ aa ] _)  ->
                mkSimpleId $ from_sml_ShATerm (getATermByIndex1 aa att)
            (ShAAppl "place" [] _)  -> mkSimpleId $ Common.Id.place
            _ -> from_sml_ShATermError "Token" aterm
            where aterm = getATerm att

instance ATermConvertibleSML Id where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "compound-id" [ aa,ab ] _)  -> -- TOKEN_OR_MIXFIX,[ID]
                let
                aa' = from_sml_ATermTokenTup (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = nullRange
                in (Id aa' ab' ac')
            (ShAAppl "simple-id" [ aa ] _) ->
                let
                aa' = from_sml_ATermTokenTup (getATermByIndex1 aa att)
                ab' = []
                ac' = nullRange
                in (Id aa' ab' ac')
            _ -> from_sml_ShATermError "Id" aterm
        where
            aterm = getATerm att

from_sml_ATermTokenTup :: ATermTable -> [Token]
from_sml_ATermTokenTup att =
    case aterm of
       (ShAAppl "" [tops,_,_] _) ->
           from_sml_ShATerm (getATermByIndex1 tops att)
       _         -> from_sml_ShATermError "Token" aterm
    where aterm = getATerm att

----- instances of AS_Annotation.hs -------------------------------------
instance ATermConvertibleSML Annotation where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "comment-line" [ aa ] _)  ->
                let
                aa' = chomp $ from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Unparsed_anno Comment_start (Line_anno aa') ab')
            (ShAAppl "comment" [ aa ] _)  ->
                let
                aa' = lines (from_sml_ShATerm (getATermByIndex1 aa att))
                ab' = pos_l
                in (Unparsed_anno Comment_start (Group_anno aa') ab')
            (ShAAppl "unparsed-anno" [ aa ] _)  ->
                parse_anno (pos_l)
                   (from_sml_ShATerm (getATermByIndex1 aa att))
            (ShAAppl "annote-line" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Unparsed_anno (Annote_word aa') (Line_anno ab') ac')
            (ShAAppl "annote-group" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Unparsed_anno (Annote_word aa') (Group_anno ab') ac')
            (ShAAppl "display-anno" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = parse_disp_anno aa' (pos_l)
                           (chomp $ from_sml_ShATerm (getATermByIndex1 ab att))
                in ab'
            (ShAAppl "string-anno" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (String_anno aa' ab' ac')
            (ShAAppl "list-anno" [ aa,ab,ac ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = from_sml_ShATerm (getATermByIndex1 ac att)
                ad' = pos_l
                in (List_anno aa' ab' ac' ad')
            (ShAAppl "number-anno" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Number_anno aa' ab')
            (ShAAppl "floating-anno" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Float_anno aa' ab' ac')
            (ShAAppl "prec-anno" [ aa,ab,ac ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = from_sml_ShATerm (getATermByIndex1 ac att)
                ad' = pos_l
                in (Prec_anno (if aa' then Lower else BothDirections)
                    ab' ac' ad')
            (ShAAppl "lassoc-anno" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Assoc_anno ALeft aa' ab')
            (ShAAppl "rassoc-anno" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Assoc_anno ARight aa' ab')
            (ShAAppl "label-anno" [ aa ] _)  ->
                let
                aa' = lines $ showId
                      (from_sml_ShATerm $ getATermByIndex1 aa att) ""
                ab' = pos_l
                in (Label aa' ab')
            (ShAAppl "implies" [] _)  ->
                let
                aa' = pos_l
                in (Semantic_anno SA_implies aa')
            (ShAAppl "definitional" [] _)  ->
                let
                aa' = pos_l
                in (Semantic_anno SA_def aa')
            (ShAAppl "conservative" [] _)  ->
                let
                aa' = pos_l
                in (Semantic_anno SA_cons aa')
            (ShAAppl "mono" [] _) ->
                Semantic_anno SA_mono (pos_l)
            _ -> from_sml_ShATermError "Annotation" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-ANNO" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

--- Well the following instance has to tie together things, that don't
--- belong to each other. Because I can't declare instances for
--- certain "Annoted types"
instance (ATermConvertibleSML a) => ATermConvertibleSML (Annoted a) where
    from_sml_ShATerm att =
        case aterm of
         (ShAAppl con as _)  ->
             (case con of
               -- Basic Items (including sig_items)
                "pos-BASIC-ITEMS" ->
                      case from_sml_ATermAnnotedBasic_Items att of
                               (bi, las) -> Annoted bi nullRange las []
               -- L_.* constuctors from SML
                ""           -> Annoted (from_sml_ShATerm (getATermByIndex1
                                                        (head as)
                                                        att))
                                             nullRange
                                             []
                                             (toAnnoList (last as) att)
                _      -> -- "No appropiate constructor for Annoted found"
                        Annoted (from_sml_ShATerm att)
                                    nullRange
                                    []
                                    []
             )
         _ -> from_sml_ShATermError "Annoted a" aterm
        where
            aterm = getATerm att

---- functions to convert annoted stuff ---------------------------------
-- all these functions are called by instance ATermConvertibleSML Annoted a

from_sml_ATermAnnotedBasic_Items :: ATermConvertibleSML a =>
                               ATermTable -> (a,[Annotation])
from_sml_ATermAnnotedBasic_Items att =
    if isSig_items then
       ((from_sml_ShATerm att),[])
    else ((from_sml_ShATerm att),annoList)
    where isSig_items =
              case aterm of
              (ShAAppl _ as _)-> -- pos-BASIC-ITEMS
                    case getATerm $ getATermByIndex1 (last as) att of
                    (ShAAppl "sig-items" _ _) -> True
                    _                         -> False
              _ -> from_sml_ShATermError "{SIG,BASIC}_items" aterm
          aterm = getATerm att
          annoList = case getATerm att of
                     (ShAAppl _ as _) -> getAnnoList (last as) att
                     _ -> error "Wrong ATerm structure: BASIC_ITEMS"

-- getAnnoList and toAnnoList are only working with an AIndex as first
-- argument is given. If getAnnoList is called every ShAAppl that starts _
-- with "pos-" is crossed without consideration. toAnnoList just calls
-- the [Annotation] conversion directly.

getAnnoList :: Int -> ATermTable -> [Annotation]
getAnnoList ai att = case at of
                     ShAAppl c as _ | isPrefixOf "pos-" c ->
                                    getAnnoList (last as) att
                     ShAAppl _ as _ -> toAnnoList (last as) att
                     _ -> error "wrong storage or missed 'pos-' contructor"
    where at = getATerm (getATermByIndex1 ai att)

toAnnoList :: Int -> ATermTable -> [Annotation]
toAnnoList ai att = from_sml_ShATerm $ getATermByIndex1 ai att

parse_anno :: Range -> String -> Annotation
parse_anno _pos_l inp =
    case parse (skip >> Common.Anno_Parser.annotations) "" inp of
       Right [x]  -> x
       _          -> error ("something strange happend to \"" ++
                             inp ++ "\" during ATerm Conversion")

parse_disp_anno :: Id -> Range -> String -> Annotation
parse_disp_anno i pos_l inp =
    case Common.Anno_Parser.parse_anno (Unparsed_anno (Annote_word "display")
                                         (Group_anno [inp']) pos_l) pos of
       Left err   -> error $ "internal parse error at " ++ show err
       Right x  -> x
    where
          pos = case rangeToList pos_l of
                  [] -> newPos "" 0 0
                  h : _ -> h
          inp' = showId i $ ' ' : s_inp
          s_inp = case reverse inp of
                  rin | "%)" `isPrefixOf` rin -> reverse $ drop 2 rin
                      | otherwise -> inp

----- instances of AS_Basic_CASL.hs -------------------------------------
instance ATermConvertibleSML (BASIC_SPEC a b c) where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "basic-spec" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                in (CASL.AS_Basic_CASL.Basic_spec aa')
            _ -> from_sml_ShATermError "BASIC_SPEC" aterm
        where
            aterm = getATerm att'
            att' =
                case getATerm att of
                (ShAAppl "pos-BASIC-SPEC" [_,item_i] _) ->
                    getATermByIndex1 item_i att
                _  -> att

instance ATermConvertibleSML (BASIC_ITEMS a b c) where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "sig-items" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                in (Sig_items aa')
            (ShAAppl "free-datatype" [ aa,_ ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Free_datatype NonEmptySorts aa' ab')
            (ShAAppl "sort-gen" [ aa,_ ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Sort_gen aa' ab')
            (ShAAppl "var-items" [ aa,_ ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Var_items aa' ab')
            (ShAAppl "local-var-axioms" [ aa,ab,_ ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Local_var_axioms aa' ab' ac')
            (ShAAppl "axiom-items" [ aa,_ ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Axiom_items aa' ab')
            _ -> from_sml_ShATermError "BASIC_ITEMS" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-BASIC-ITEMS" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML (SIG_ITEMS a b) where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "sort-items" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                as  = from_sml_ShATerm (getATermByIndex1 ab att)
                aa'' = (addLAnnoList as $ head aa'):(tail aa')
                ab' = pos_l
                in (Sort_items NonEmptySorts aa'' ab')
            (ShAAppl "op-items" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                as  = from_sml_ShATerm (getATermByIndex1 ab att)
                aa'' = (addLAnnoList as $ head aa'):(tail aa')
                ab' = pos_l
                in (Op_items aa'' ab')
            (ShAAppl "pred-items" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                as  = from_sml_ShATerm (getATermByIndex1 ab att)
                aa'' = (addLAnnoList as $ head aa'):(tail aa')
                ab' = pos_l
                in (Pred_items aa'' ab')
            (ShAAppl "datatype-items" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                as  = from_sml_ShATerm (getATermByIndex1 ab att)
                aa'' = (addLAnnoList as $ head aa'):(tail aa')
                ab' = pos_l
                in (Datatype_items NonEmptySorts aa'' ab')
            _ -> from_sml_ShATermError "SIG_ITEMS" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-SIG-ITEMS" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML (SORT_ITEM a) where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "sort-decl" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Sort_decl aa' ab')
            (ShAAppl "subsort-decl" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Subsort_decl aa' ab' ac')
            (ShAAppl "subsort-defn" [ aa,ab,ac,ad,ae ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ATermSIMPLE_ID (getATermByIndex1 ab att)
                ac' = from_sml_ShATerm (getATermByIndex1 ac att)
                ad' = from_sml_ShATerm (getATermByIndex1 ad att)
                as  = toAnnoList ae att
                ad''= addRAnnoList as ad'
                ae' = pos_l
                in (Subsort_defn aa' ab' ac' ad'' ae')
            (ShAAppl "iso-decl" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Iso_decl aa' ab')
            _ -> from_sml_ShATermError "SORT_ITEM" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-SORT-ITEM" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML (OP_ITEM a) where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "op-decl" [ aa,ab,ac ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = from_sml_ShATerm (getATermByIndex1 ac att)
                ad' = pos_l
                in (Op_decl aa' ab' ac' ad')
            (ShAAppl "op-defn" [ aa,ab,ac,ad ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = from_sml_ShATerm (getATermByIndex1 ac att)
                as  = from_sml_ShATerm (getATermByIndex1 ad att)
                ac''= addRAnnoList as ac'
                ad' = pos_l
                in (Op_defn aa' ab' ac'' ad')
            _ -> from_sml_ShATermError "OP_ITEM" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-OP-ITEM" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML OP_TYPE where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "total-op-type" [ aa,ab ] _)  ->
                let
                (aa',ps) = from_sml_ATermSORTS (getATermByIndex1 aa att)
                ab'      = from_sml_ShATerm (getATermByIndex1 ab att)
                ac'      = insertPos ps $ pos_l
                in (Op_type Total aa' ab' ac')
            (ShAAppl "partial-op-type" [ aa,ab ] _)  ->
                let
                (aa',ps) = from_sml_ATermSORTS (getATermByIndex1 aa att)
                ab'      = from_sml_ShATerm (getATermByIndex1 ab att)
                ac'      = insertPos ps $ pos_l
                in (Op_type Partial aa' ab' ac')
            _ -> from_sml_ShATermError "OP_TYPE" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-OP-TYPE" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

---- a helper for the SML-datatype SORTS -------------------------------
from_sml_ATermSORTS :: ATermTable -> ([SORT],Range)
from_sml_ATermSORTS att =
        case aterm of
            (ShAAppl "sorts" [ aa ] _)  ->
                (from_sml_ShATerm (getATermByIndex1 aa att),pos_l)
            _ -> from_sml_ShATermError "([SORT],Range)" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-SORTS" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML OP_HEAD where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "total-op-head" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Op_head Total aa' ab' ac')
            (ShAAppl "partial-op-head" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Op_head Partial aa' ab' ac')
            _ -> from_sml_ShATermError "OP_HEAD" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-OP-HEAD" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML ARG_DECL where
    from_sml_ShATerm att =
        case aterm of
--  (ShAAppl "arg-decl" [ ShAAppl "" [aa,ab] _ ] _)  ->
        (ShAAppl "" [aa,ab] _)  ->
                let
                aa' = from_sml_ATermVARs (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Arg_decl aa' ab' ac')
        _                       -> from_sml_ShATermError "ARG_DECL" aterm
        where
            aterm = case getATerm att' of
                    ShAAppl "arg-decl" [i] _ ->
                            getATerm $ getATermByIndex1 i att
                    x         -> from_sml_ShATermError "arg-decl" x
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-ARG-DECL" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML (OP_ATTR a) where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "associative" [ ] _)  ->
                let
                in Assoc_op_attr
            (ShAAppl "commutative" [ ] _)  ->
                let
                in Comm_op_attr
            (ShAAppl "idempotent" [ ] _)  ->
                let
                in Idem_op_attr
            (ShAAppl "unit-op-attr" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                in (Unit_op_attr aa')
            _ -> from_sml_ShATermError "OP_ATTR" aterm
        where
            aterm = getATerm att'
            att' =
                case getATerm att of
                (ShAAppl "pos-OP-ATTR" [_,item_i] _) ->
                    getATermByIndex1 item_i att
                _  -> att

instance ATermConvertibleSML (PRED_ITEM a) where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "pred-decl" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Pred_decl aa' ab' ac')
            (ShAAppl "pred-defn" [ aa,ab,ac,_ ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = from_sml_ShATerm (getATermByIndex1 ac att)
                ad' = pos_l
                in (Pred_defn aa' ab' ac' ad')
            _ -> from_sml_ShATermError "PRED_ITEM" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-PRED-ITEM" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML PRED_TYPE where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "pred-type" [ aa ] _)  ->
                let
                (aa',ps) = from_sml_ATermSORTS (getATermByIndex1 aa att)
                ab'      = insertPos ps $ pos_l
                in (Pred_type aa' ab')
            _ -> from_sml_ShATermError "PRED_TYPE" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-PRED-TYPE" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML PRED_HEAD where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "pred-head" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Pred_head aa' ab')
            _ -> from_sml_ShATermError "PRED_HEAD" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-PRED-HEAD" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML DATATYPE_DECL where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "datatype-decl" [ aa,ab,ac ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                as  = from_sml_ShATerm (getATermByIndex1 ac att)
                ab''= (addLAnnoList as $ head ab'):(tail ab')
                ac' = pos_l
                in (Datatype_decl aa' ab'' ac')
            _ -> from_sml_ShATermError "DATATYPE_DECL" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-DATATYPE-DECL" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML ALTERNATIVE where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "total-construct" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Alt_construct Total aa' ab' ac')
            (ShAAppl "partial-construct" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Alt_construct Partial aa' ab' ac')
            (ShAAppl "subsort" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Subsorts aa' ab')
            _ -> from_sml_ShATermError "ALTERNATIVE" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-ALTERNATIVE" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML COMPONENTS where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "total-select" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Cons_select Total aa' ab' ac')
            (ShAAppl "partial-select" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Cons_select Partial aa' ab' ac')
            (ShAAppl "sort-component" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                in (Sort aa')
            _ -> from_sml_ShATermError "COMPONENTS" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-COMPONENTS" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML VAR_DECL where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ATermVARs (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                in (Var_decl aa' ab' nullRange)
            _ -> from_sml_ShATermError "VAR_DECL" aterm
        where
            aterm = getATerm att

instance ATermConvertibleSML (FORMULA a) where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "quantification" [ aa,ab,ac ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                pq  = getPos (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = from_sml_ShATerm (getATermByIndex1 ac att)
                ad' = insertPos pq $ pos_l
                in (Quantification aa' ab' ac' ad')
            (ShAAppl "conjunction" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Conjunction aa' ab')
            (ShAAppl "disjunction" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Disjunction aa' ab')
            (ShAAppl "implication" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Implication aa' ab' True ac')
            (ShAAppl "equivalence" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Equivalence aa' ab' ac')
            (ShAAppl "negation" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Negation aa' ab')
            -- the following things are from SML-type ATOM
            (ShAAppl "atom" [i] _) ->
              case getATerm (getATermByIndex1 i att') of
               (ShAAppl "ttrue" [] _) ->
                 let
                 aa' = pos_l
                 in (True_atom aa')
               (ShAAppl "ffalse" [] _) ->
                 let
                 aa' = pos_l
                 in (False_atom aa')
               (ShAAppl "predication" [ aa,ab ] _) ->
                 let
                 aa'      = from_sml_ShATerm (getATermByIndex1 aa att)
                 (ab',ps) = from_sml_ATermTERMS (getATermByIndex1 ab att)
                 ac'      = insertPos ps $ pos_l
                 in (Predication aa' ab' ac')
               (ShAAppl "definedness" [ aa ] _) ->
                 let
                 aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                 ab' = pos_l
                 in (Definedness aa' ab')
               (ShAAppl "existl-equation" [ aa,ab ] _) ->
                 let
                 aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                 ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                 ac' = pos_l
                 in (Existl_equation aa' ab' ac')
               (ShAAppl "strong-equation" [ aa,ab ] _) ->
                 let
                 aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                 ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                 ac' = pos_l
                 in (Strong_equation aa' ab' ac')
               (ShAAppl "membership" [ aa,ab ] _) ->
                 let
                 aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                 ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                 ac' = pos_l
                 in (Membership aa' ab' ac')
               _ -> from_sml_ShATermError "FORMULA" aterm
            _ -> from_sml_ShATermError "FORMULA" aterm
        where
            aterm = getATerm att'
            (pos_l,_g_flag,att') = skipPosFlag "pos-FORMULA" att

---- a helper for the SML-datatype TERMS -------------------------------
from_sml_ATermTERMS :: ATermTable -> ([TERM a],Range)
from_sml_ATermTERMS att =
    case aterm of
             (ShAAppl "terms" [ aa ] _)  ->
                 (from_sml_ShATerm (getATermByIndex1 aa att),pos_l)
             _ -> from_sml_ShATermError "([TERM],Range)" aterm
    where aterm = getATerm att'
          (pos_l,att') =
              case getATerm att of
              (ShAAppl "pos-TERMS" [reg_i,item_i] _) ->
                       (posFromRegion reg_i att,getATermByIndex1 item_i att)
              _  -> (nullRange,att)

---- a helper for SIMPLE_IDs --------------------------------------------

from_sml_ATermSIMPLE_ID :: ATermTable -> SIMPLE_ID
from_sml_ATermSIMPLE_ID att =
    case aterm of
      (ShAAppl "" [ si, _ ] _) -> -- snd element is 'None'
                                  -- (CASL.grm:((WORDS,None)))
          let s = from_sml_ShATerm $ getATermByIndex1 si att
          in mkSimpleId s
      _ -> from_sml_ShATermError "SIMPLE_ID" aterm
    where aterm = getATerm att

---- a helper for [VAR] -------------------------------------------------
from_sml_ATermVARs :: ATermTable -> [VAR]
from_sml_ATermVARs att = map from_sml_ATermSIMPLE_ID att_list
    where att_list = case getATerm att of
                     ShAList l _-> map getAtt l
                     _          -> from_sml_ShATermError "[VAR]" $ getATerm att
          getAtt ai = getATermByIndex1 ai att

instance ATermConvertibleSML QUANTIFIER where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "forall" [ ] _)  ->
                let
                in Universal
            (ShAAppl "exists" [ ] _)  ->
                let
                in Existential
            (ShAAppl "exists-uniquely" [ ] _)  ->
                let
                in Unique_existential
            _ -> from_sml_ShATermError "QUANTIFIER" aterm
        where
            aterm = getATerm att'
            att' =
                case getATerm att of
                (ShAAppl "pos-QUANTIFIER" [_,item_i] _) ->
                    getATermByIndex1 item_i att
                _  -> att

instance ATermConvertibleSML PRED_SYMB where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "pred-symb" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                in case getATerm $ getATermByIndex1 ab att of
                   ShAAppl "None" [] _ ->
                       (Pred_name aa')
                   ShAAppl "Some" [ aab ] _ ->
                     let aab' = from_sml_ShATerm (getATermByIndex1 aab att)
                         ac' = pos_l
                     in (Qual_pred_name aa' aab' ac')
                   _ -> from_sml_ShATermError "Option" aterm
            _ -> from_sml_ShATermError "PRED_SYMB" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-PRED-SYMB" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML (TERM a) where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "var-or-const" [ aa ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                in varOrConst aa'
            (ShAAppl "qual-var" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Qual_var aa' ab' ac')
            (ShAAppl "application" [ aa,ab ] _)  ->
                let
                aa'      = from_sml_ShATerm (getATermByIndex1 aa att)
                (ab',ps) = from_sml_ATermTERMS (getATermByIndex1 ab att)
                ac'      = insertPos ps $ pos_l
                in (Application aa' ab' ac')
            (ShAAppl "sorted-term" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Sorted_term aa' ab' ac')
            (ShAAppl "cast" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Cast aa' ab' ac')
            (ShAAppl "conditional" [ aa,ab,ac ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = from_sml_ShATerm (getATermByIndex1 ac att)
                ad' = pos_l
                in (Conditional aa' ab' ac' ad')
            _ -> from_sml_ShATermError "TERM" aterm
        where
            aterm = getATerm att'
            (pos_l,_p_flag,att') = skipPosFlag "pos-TERM" att

instance ATermConvertibleSML OP_SYMB where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "op-symb" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                in case getATerm $ getATermByIndex1 ab att of
                   ShAAppl "None" [] _ ->
                       (Op_name aa')
                   ShAAppl "Some" [ aab ] _ ->
                     let aab' = from_sml_ShATerm (getATermByIndex1 aab att)
                         ac' = pos_l
                     in (Qual_op_name aa' aab' ac')
                   _ -> from_sml_ShATermError "Option" aterm
            _ -> from_sml_ShATermError "OP_SYMB" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-OP-SYMB" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML SYMB_ITEMS where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "symb-items" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Symb_items aa' ab' ac')
            _ -> from_sml_ShATermError "SYMB_ITEMS" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-SYMB-ITEMS" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML SYMB_MAP_ITEMS where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "symb-map-items" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Symb_map_items aa' ab' ac')
            _ -> from_sml_ShATermError "SYMB_MAP_ITEMS" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-SYMB-MAP-ITEMS" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML SYMB_KIND where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "implicitk" [ ] _)  ->
                Implicit
            (ShAAppl "sortsk" [ ] _)  ->
                Sorts_kind
            (ShAAppl "opsk" [ ] _)  ->
                Ops_kind
            (ShAAppl "predsk" [ ] _)  ->
                Preds_kind
            _ -> from_sml_ShATermError "SYMB_KIND" aterm
        where
            aterm = getATerm att'
            att' =
                case getATerm att of
                (ShAAppl "pos-SYMB-KIND" [_,item_i] _) ->
                    getATermByIndex1 item_i att
                _  -> att

instance ATermConvertibleSML SYMB where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "symb-id" [ aa ] _)  ->
                let
                i  = from_sml_ShATerm (getATermByIndex1 aa att)
                aa' = setFstPos (pos_l) i
                in (Symb_id aa')
            (ShAAppl "qual-id" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Qual_id aa' ab' ac')
            _ -> from_sml_ShATermError "SYMB" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-SYMB" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML TYPE where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "op-symb-type" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                in (O_type aa')
            (ShAAppl "pred-symb-type" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                in (P_type aa')
            _ -> from_sml_ShATermError "TYPE" aterm
        where
            aterm = getATerm att'
            att' =
                case getATerm att of
                (ShAAppl "pos-TYPE" [_,item_i] _) ->
                    getATermByIndex1 item_i att
                _  -> att

instance ATermConvertibleSML SYMB_OR_MAP where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "symb" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                in (Symb aa')
            (ShAAppl "symb-or-map" [ aa ] _)  ->
                let
                (aa',ab') = from_sml_ATermSYMB_MAP (getATermByIndex1 aa att)
                ac' = pos_l
                in (Symb_map aa' ab' ac')
            _ -> from_sml_ShATermError "SYMB_OR_MAP" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-SYMB-OR-MAP" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

---- a helper for SYMB_MAP from SML -------------------------------------

from_sml_ATermSYMB_MAP :: ATermTable -> (SYMB,SYMB)
from_sml_ATermSYMB_MAP att =
        case aterm of
            (ShAAppl "symb-map" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                in (aa',ab')
            _ -> from_sml_ShATermError "(SYMB,SYMB)" aterm
        where
            aterm = getATerm att'
            att' =
                case getATerm att of
                (ShAAppl "pos-SYMB-MAP" [_,item_i] _) ->
                    getATermByIndex1 item_i att
                _  -> att

----- instances of AS_Structured.hs -------------------------------------
instance ATermConvertibleSML SPEC where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "basic" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                aa'' = G_basic_spec CASL aa'
                in group (Syntax.AS_Structured.Basic_spec aa''
                          nullRange) group_flag
            (ShAAppl "translation" [ aa,ab,_ ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                in group (Translation aa' ab') group_flag
            (ShAAppl "reduction" [ aa,ab,_ ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                in group (Reduction aa' ab') group_flag
            (ShAAppl "union-spec" [ aa ] _)  ->
                let
                aa' :: [(Annoted SPEC,[Annotation])]
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in group (Union (toAnnotedList aa') ab') group_flag
            (ShAAppl "extension" [ aa ] _)  ->
                let
                aa' :: [(Annoted SPEC,[Annotation])]
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in group (Extension (toAnnotedList aa') ab') group_flag
            (ShAAppl "free-spec" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                aa''= addLAnnoList (toAnnoList ab att) aa'
                ab' = pos_l
                in group (Free_spec aa'' ab') group_flag
            (ShAAppl "local-spec" [ aa,ab,ac,ad ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                sp1 = addLAnnoList (toAnnoList ab att) aa'
                ac' = from_sml_ShATerm (getATermByIndex1 ac att)
                sp2 = addLAnnoList (toAnnoList ad att) ac'
                in group (Local_spec sp1 sp2 pos_l) group_flag
            (ShAAppl "closed-spec" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                aa''= addLAnnoList (toAnnoList ab att) aa'
                ab' = pos_l
                in group (Closed_spec aa'' ab') group_flag
            (ShAAppl "spec-inst" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                in (Spec_inst aa' ab' nullRange)
            _ -> from_sml_ShATermError "SPEC" aterm
        where
            aterm = getATerm att'
            group s gf = if gf then (Group s' pos_l) else s
                where s' = Annoted s nullRange [] []
            (pos_l,group_flag,att') = skipPosFlag "pos-SPEC" att

--- a helper function for [(Annoted a, [Annotation])] --------------------

toAnnotedList :: [(Annoted a,[Annotation])] -> [Annoted a]
toAnnotedList xs = map merge xs
    where merge (ai,as) = ai { l_annos = (l_annos ai) ++ as}

instance ATermConvertibleSML RENAMING where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "renaming" [ aa ] _)  ->
              case from_sml_ShATerm (getATermByIndex1 aa att) of
              aa' -> let
                aa''= if null aa' then []
                      else [G_symb_map $ G_symb_map_items_list CASL aa']
                ab' = pos_l
                in (Renaming aa'' ab')
            _ -> from_sml_ShATermError "RENAMING" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-RENAMING" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML RESTRICTION where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "hide" [ aa ] _)  ->
                let
                aa''= case from_sml_ShATerm (getATermByIndex1 aa att) of
                      [] -> []
                      aa' -> [G_symb_list $ G_symb_items_list CASL aa']
                ab' = pos_l
                in (Hidden aa'' ab')
            (ShAAppl "reveal" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                aa''= G_symb_map_items_list CASL aa'
                ab' = pos_l
                in (Revealed aa'' ab')
            _ -> from_sml_ShATermError "RESTRICTION" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-RESTRICTION" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

{- !!! This will be done by the instance of LIB_ITEM !!!
instance ATermConvertibleSML SPEC_DEFN where
-}

instance ATermConvertibleSML GENERICITY where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "genericity" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Genericity aa' ab' ac')
            _ -> from_sml_ShATermError "GENERICITY" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-GENERICITY" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML PARAMS where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "params" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                in (Params aa')
            _ -> from_sml_ShATermError "PARAMS" aterm
        where
            aterm = getATerm att'
            att' =
                case getATerm att of
                (ShAAppl "pos-PARAMS" [_,item_i] _) ->
                    getATermByIndex1 item_i att
                _  -> att

instance ATermConvertibleSML IMPORTED where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "imports" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                in (Imported aa')
            _ -> from_sml_ShATermError "IMPORTED" aterm
        where
            aterm = getATerm att'
            att' =
                case getATerm att of
                (ShAAppl "pos-IMPORTS" [_,item_i] _) ->
                    getATermByIndex1 item_i att
                _  -> att

instance ATermConvertibleSML FIT_ARG where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "fit-spec" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab''= case from_sml_ShATerm (getATermByIndex1 ab att) of
                      [] -> []
                      ab' -> [G_symb_map $ G_symb_map_items_list CASL ab']
                ac' = pos_l
                in (Fit_spec aa' ab'' ac')
            (ShAAppl "fit-view" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Fit_view aa' ab' ac')
            _ -> from_sml_ShATermError "FIT_ARG" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-FIT-ARG" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)
{- !!! This conversion is covered by the instance of LIB_ITEM !!!

instance ATermConvertibleSML VIEW_DEFN where
-}

instance ATermConvertibleSML VIEW_TYPE where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "view-type" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (View_type aa' ab' ac')
            _ -> from_sml_ShATermError "VIEW_TYPE" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-VIEW-TYPE" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

----- instances of AS_Architecture.hs -----------------------------------
{- !!! This conversion is covered by the instance of LIB_ITEM !!!
instance ATermConvertibleSML ARCH_SPEC_DEFN where
-}

instance ATermConvertibleSML ARCH_SPEC where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "basic-arch-spec" [ aa,ab,ac ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ATermRESULT_UNIT (getATermByIndex1 ab att)
                as  = toAnnoList ac att
                aa''= (addLAnnoList as $ head aa'):tail aa'
                ac' = pos_l
                in (Basic_arch_spec aa'' ab' ac')
            (ShAAppl "named-arch-spec" [ aa ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                in (Arch_spec_name aa')
            _ -> from_sml_ShATermError "ARCH_SPEC" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-ARCH-SPEC" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

from_sml_ATermRESULT_UNIT :: ATermTable -> (Annoted UNIT_EXPRESSION)
from_sml_ATermRESULT_UNIT att =
        case aterm of
            (ShAAppl "result-unit" [ aa,ab ] _)  ->
                let
--              aa' :: UNIT_EXPRESSION
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                as  = toAnnoList ab att
                in (Annoted aa' nullRange as [])
            _ -> from_sml_ShATermError "RESULT-UNIT" aterm
        where
            aterm = getATerm att'
            att' =
                case getATerm att of
                (ShAAppl "pos-RESULT-UNIT" [_,item_i] _) ->
                    getATermByIndex1 item_i att
                _  -> att

instance ATermConvertibleSML UNIT_REF where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "unit-decl-case" [ udl ] _)  ->
                let att1 = getATermByIndex1 udl att
                    (ps,att2) = case getATerm att1 of
                                  (ShAAppl "pos-UNIT-DECL" [reg_i,item_i] _) ->
                                      (posFromRegion reg_i att,
                                       getATermByIndex1 item_i att1)
                                  _  -> (nullRange,att1)
                    aterm2 = getATerm att2
                in case aterm2 of
                   ShAAppl "unit-decl" [aa,ab,_] _ ->
                      let aa'  = from_sml_ATermSIMPLE_ID $
                               getATermByIndex1 aa att
                          ab'  = from_sml_ShATerm (getATermByIndex1 ab att)
                          ad'  = ps
                      in (Unit_ref aa' ab' ad')
                   _ -> from_sml_ShATermError "UNIT_DECL" aterm2
            _ -> from_sml_ShATermError "UNIT-DECL-DEFN" aterm
        where
            aterm = getATerm att'
            att' =
                case getATerm att of
                (ShAAppl "pos-UNIT-DECL-DEFN" [_,item_i] _) ->
                    getATermByIndex1 item_i att
                _  -> att

instance ATermConvertibleSML UNIT_DECL_DEFN where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "unit-decl-case" [ udl ] _)  ->
                let att1 = getATermByIndex1 udl att
                    (ps,att2) = case getATerm att1 of
                                  (ShAAppl "pos-UNIT-DECL" [reg_i,item_i] _) ->
                                      (posFromRegion reg_i att,
                                       getATermByIndex1 item_i att1)
                                  _  -> (nullRange,att1)
                    aterm2 = getATerm att2
                in case aterm2 of
                   ShAAppl "unit-decl" [aa,ab,ac] _ ->
                    let aa' = from_sml_ATermSIMPLE_ID $ getATermByIndex1 aa att
                        ab' = from_sml_ShATerm $ getATermByIndex1 ab att
                        ac' = from_sml_ATermUNIT_IMPORTS $
                                         getATermByIndex1 ac att
                        ad' = ps
                    in Unit_decl aa' ab' ac' ad'
                   _ -> from_sml_ShATermError "UNIT_DECL" aterm2
            (ShAAppl "unit-defn-case" [ udn ] _)  ->
                from_sml_ATermUNIT_DEFN $ getATermByIndex1 udn att
            (ShAAppl "pos-UNIT-DEFN" _ _) ->
                from_sml_ATermUNIT_DEFN att
            (ShAAppl "unit-defn" _ _) ->
                from_sml_ATermUNIT_DEFN att
            _ -> from_sml_ShATermError "UNIT-DECL-DEFN" aterm
        where
            aterm = getATerm att'
            att' =
                case getATerm att of
                (ShAAppl "pos-UNIT-DECL-DEFN" [_,item_i] _) ->
                    getATermByIndex1 item_i att
                _  -> att

---- a helper for the SML-datatype UNIT_IMPORTS ------------------------

from_sml_ATermUNIT_IMPORTS :: ATermTable -> [Annoted UNIT_TERM]
from_sml_ATermUNIT_IMPORTS att =
    case aterm of
             (ShAAppl "unit-imports" [ aa ] _)  ->
                 from_sml_ShATerm $ getATermByIndex1 aa att
             _ -> from_sml_ShATermError "UNIT_IMPORTS" aterm
    where aterm = getATerm att'
          att' =
              case getATerm att of
              (ShAAppl "pos-UNIT-IMPORTS" [_,item_i] _) ->
                  getATermByIndex1 item_i att
              _  -> att

from_sml_ATermUNIT_DEFN :: ATermTable -> UNIT_DECL_DEFN
from_sml_ATermUNIT_DEFN att =
    case aterm of
    ShAAppl "unit-defn" [aa,ab] _ ->
        let aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
            ab' = from_sml_ShATerm (getATermByIndex1 ab att)
            ac' = ps
        in (Unit_defn aa' ab' ac')
    _ -> from_sml_ShATermError "UNIT_DEFN" aterm
    where aterm = getATerm att'
          (ps,att') =
              case getATerm att of
              (ShAAppl "pos-UNIT-DEFN" [reg_i,item_i] _) ->
                  (posFromRegion reg_i att,getATermByIndex1 item_i att)
              _  -> (nullRange,att)

{- !!! This conversion is covered by the instance of LIB_ITEM !!!
instance ATermConvertibleSML UNIT_SPEC_DEFN where
-}

instance ATermConvertibleSML UNIT_SPEC where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "unit-type-case" [ aa ] _)  ->
                let
                (aa',ab') = from_sml_ATermUNIT_TYPE $ getATermByIndex1 aa att
                ac' = pos_l
                in (Unit_type aa' ab' ac')
            (ShAAppl "spec-name-case" [ aa ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                in (Spec_name aa')
            (ShAAppl "closed" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Closed_unit_spec aa' ab')
            _ -> from_sml_ShATermError "UNIT_SPEC" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-UNIT-SPEC" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML REF_SPEC where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "unit-type-case" [ aa ] _)  ->
                let
                (aa',ab') = from_sml_ATermUNIT_TYPE $ getATermByIndex1 aa att
                ac' = pos_l
                in Unit_spec $ Unit_type aa' ab' ac'
            (ShAAppl "spec-name-case" [ aa ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                in (Unit_spec $ Spec_name aa')
            (ShAAppl "arch-spec-case" [ aa,ab ] _)  ->
                let
                aa'   = from_sml_ShATerm (getATermByIndex1 aa att)
                ps    = toAnnoList ab att
                aa''  = addLAnnoList ps aa'
                ab'   = pos_l
                aa''' = case aa'' of
                        (Annoted (Basic_arch_spec _ _ _) _ _ _) ->
                            Annoted (Group_arch_spec aa'' ab') nullRange [][]
                        _ -> aa''
                in (Arch_unit_spec aa''' ab')
            (ShAAppl "closed" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Unit_spec $ Closed_unit_spec aa' ab')
            _ -> from_sml_ShATermError "UNIT_SPEC" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-UNIT-SPEC" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

---- a helper for the SML-datatype UNIT_TYPE ----------------------------

from_sml_ATermUNIT_TYPE :: ATermTable -> ([Annoted SPEC],(Annoted SPEC))
from_sml_ATermUNIT_TYPE att =
    case aterm of
             (ShAAppl "unit-type" [ aa,ab ] _)  ->
                 (from_sml_ShATerm $ getATermByIndex1 aa att,
                  from_sml_ShATerm $ getATermByIndex1 ab att)
             _ -> from_sml_ShATermError "UNIT_TYPE" aterm
    where aterm = getATerm att'
          att' =
              case getATerm att of
              (ShAAppl "pos-UNIT-TYPE" [_,item_i] _) ->
                  getATermByIndex1 item_i att
              _  -> att

instance ATermConvertibleSML UNIT_EXPRESSION where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "unit-expression" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Unit_expression aa' ab' ac')
            _ -> from_sml_ShATermError "UNIT_EXPRESSION" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-UNIT-EXPRESSION" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML UNIT_BINDING where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "unit-binding" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Unit_binding aa' ab' ac')
            _ -> from_sml_ShATermError "UNIT_BINDING" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-UNIT-BINDING" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML UNIT_TERM where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "unit-reduction" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                in group (Unit_reduction aa' ab') group_flag
            (ShAAppl "unit-translation" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                in group (Unit_translation aa' ab') group_flag
            (ShAAppl "amalgamation" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in group (Amalgamation aa' ab') group_flag
            (ShAAppl "local-unit" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in group (Local_unit aa' ab' ac') group_flag
            (ShAAppl "unit-appl" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in group (Unit_appl aa' ab' ac') group_flag
            _ -> from_sml_ShATermError "UNIT_TERM" aterm
        where
            aterm = getATerm att'
            group ut gf = if gf then (Group_unit_term ut' pos_l) else ut
                where ut' = Annoted ut nullRange [] []
            (pos_l,group_flag,att') = skipPosFlag "pos-UNIT-TERM" att

instance ATermConvertibleSML FIT_ARG_UNIT where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "fit-arg-unit" [ aa,ab ] _)  ->
                case from_sml_ShATerm (getATermByIndex1 aa att) of
                aa' -> case from_sml_ShATerm (getATermByIndex1 ab att) of
                    ab' -> Fit_arg_unit aa' (if null ab' then [] else
                      [G_symb_map $ G_symb_map_items_list CASL ab']) $ pos_l
            _ -> from_sml_ShATermError "FIT_ARG_UNIT" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-FIT-ARG-UNIT" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

----- instances of AS_LIbrary.hs ----------------------------------------
instance ATermConvertibleSML LIB_DEFN where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "lib-defn" [ aa,ab,ad ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                ad' = from_sml_ShATerm (getATermByIndex1 ad att)
                in (Lib_defn aa' ab' ac' ad')
            _ -> from_sml_ShATermError "LIB_DEFN" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-LIB-DEFN" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML LIB_ITEM where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "spec-defn" [ aa,ab,ac,ad ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = from_sml_ShATerm (getATermByIndex1 ac att)
                as  = toAnnoList ad att
                ac''= addLAnnoList as ac'
                ad' = pos_l
                in Syntax.AS_Library.Spec_defn aa' ab' ac'' ad'
            (ShAAppl "view-defn" [ aa,ab,ac,ad,_ ] _)  ->
                let  -- the annotation list is lost !!!!
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = from_sml_ShATerm (getATermByIndex1 ac att)
                ad''= case from_sml_ShATerm (getATermByIndex1 ad att) of
                      [] -> []
                      ad' -> [G_symb_map $ G_symb_map_items_list CASL ad']
                ae' = pos_l
                in (Syntax.AS_Library.View_defn aa' ab' ac' ad'' ae')
            (ShAAppl "arch-spec-defn" [ aa,ab,_ ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Syntax.AS_Library.Arch_spec_defn aa' ab' ac')
            (ShAAppl "unit-spec-defn" [ aa,ab,_ ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Syntax.AS_Library.Unit_spec_defn aa' ab' ac')
            (ShAAppl "download-items" [ aa,ab,_ ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Syntax.AS_Library.Download_items aa' ab' ac')
            _ -> from_sml_ShATermError "LIB_ITEM" aterm
        where
            aterm = getATerm att'
            (pos_l,att') = skipPos "pos-LIB-ITEM" att

---- helpers to skip nested "pos-"-constructors -----------------------
skipPos :: String -> ATermTable -> (Range,ATermTable)
skipPos mcon at   =
     case getATerm at of
              ShAAppl con [reg_i,item_i] _ | mcon == con ->
                  if pCon then skipPos mcon at'
                  else (posFromRegion (reg_i) at, at')
                      where pCon = case getATerm at' of
                                   ShAAppl con' _ _ | mcon == con' -> True
                                   _                               -> False
                            at'  = getATermByIndex1 item_i at
              _  -> (nullRange,at)

skipPosFlag :: String -> ATermTable -> (Range,Bool,ATermTable)
skipPosFlag mcon att   =
    case getATerm att of
    ShAAppl con [reg_i,b_i,item_i] _ | mcon == con ->
          if pCon then let (_r_pos_l,r_b,r_at') = skipPosFlag mcon at'
                       in (pos_l,r_b || b,r_at')
          else (pos_l,b,at')
              where pCon  = case getATerm at' of
                            ShAAppl con' _ _ | mcon == con' -> True
                            _                           -> False
                    at'   = getATermByIndex1 item_i att
                    pos_l = posFromRegion reg_i att
                    b     = from_sml_ShATerm $ getATermByIndex1 b_i att
    _  -> (nullRange,False,att)

instance ATermConvertibleSML ITEM_NAME_OR_MAP where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "item-name" [ aa ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                in (Item_name aa')
            (ShAAppl "item-name-map" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ATermSIMPLE_ID (getATermByIndex1 aa att)
                ab' = from_sml_ATermSIMPLE_ID (getATermByIndex1 ab att)
                ac' = pos_l
                in (Item_name_map aa' ab' ac')
            _ -> from_sml_ShATermError "ITEM_NAME_OR_MAP" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-ITEM-NAME-OR-MAP" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML LIB_NAME where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "versioned-lib" [ aa,ab ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = from_sml_ShATerm (getATermByIndex1 ab att)
                in (Lib_version aa' ab')
            (ShAAppl "lib" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                in (Lib_id aa')
            _ -> from_sml_ShATermError "LIB_NAME" aterm
        where
            aterm = getATerm att'
            att' =
                case getATerm att of
                (ShAAppl "pos-LIB-NAME" [_,item_i] _) ->
                    getATermByIndex1 item_i att
                _  -> att

instance ATermConvertibleSML LIB_ID where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "url" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Direct_link aa' ab')
            (ShAAppl "path-name" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Indirect_link aa' ab' "" noTime)
            _ -> from_sml_ShATermError "LIB_NAME" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-LIB-ID" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)

instance ATermConvertibleSML VERSION_NUMBER where
    from_sml_ShATerm att =
        case aterm of
            (ShAAppl "version" [ aa ] _)  ->
                let
                aa' = from_sml_ShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Version_number aa' ab')
            _ -> from_sml_ShATermError "VERSION_NUMBER" aterm
        where
            aterm = getATerm att'
            (pos_l,att') =
                case getATerm att of
                (ShAAppl "pos-VERSION" [reg_i,item_i] _) ->
                    (posFromRegion reg_i att,getATermByIndex1 item_i att)
                _  -> (nullRange,att)
-------------------------------------------------------------------------

-- some helpers for Annoted things --------------------------------------
addLAnnoList :: [Annotation] -> Annoted a -> Annoted a
addLAnnoList as ani = ani {l_annos = as ++ (l_annos ani) }

addRAnnoList :: [Annotation] -> Annoted a -> Annoted a
addRAnnoList as ani = ani {r_annos = (r_annos ani) ++ as }

--- some helpers for Regions and Positions ------------------------------

posFromRegion :: Int -> ATermTable -> Range
posFromRegion reg at = Range $ map ( \ (l, c) -> newPos "" l c )
                             $ from_sml_ATerm_reg reg at

getPos :: ATermTable -> Range
getPos att = case getATerm att of
                ShAAppl _ (x:_) _ -> posFromRegion x att
                _       -> nullRange

-- converts an aterm region information to Range
from_sml_ATerm_reg :: Int -> ATermTable -> [(Int,Int)]
from_sml_ATerm_reg reg_i at = [fst r,snd r]
    where r :: ((Int,Int),(Int,Int)) -- Id.hs Region
          r = from_sml_ShATerm r_at
          r_at = getATermByIndex1 reg_i at

insertIM, insertPosAux :: [a] -> [a] -> [a]
insertIM ips ops | even $ length ops = let hl = (length ops) `div` 2
                                           (fp,lp) = splitAt hl ops
                                       in fp ++ ips ++ lp
                 | otherwise = error
                               "wrong call: length of snd list must be even"
insertPosAux = insertIM

insertPos :: Range -> Range -> Range
insertPos (Range l1) (Range l2) = Range (insertPosAux l1 l2)

setFstPos :: Range -> Id -> Id
setFstPos (Range (p:_)) i = case i of
                       Id tops ids pos_l ->
                           Id (setFstPos' tops) ids pos_l
    where setFstPos' tops | null tops = []
                          | otherwise = (ftop):(tail tops)
              where ftop = (head tops) { tokPos = Range [p] }
setFstPos _ _ = error "wrong call: setFstPos"
