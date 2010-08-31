{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Parser where

import Parsec
import ParsecExpr
import Structured

hetParse :: LogicGraph -> String -> SPEC
hetParse (logics@((_,defaultLogic):_), translations) input =
  case (runParser spec defaultLogic "" input) of
         Left err -> error ("parse error at "++show err)
         Right x  -> x
  where
  spec    :: CharParser AnyLogic SPEC
  spec    = buildExpressionParser table basic
          <?> "SPEC"
  basic = do { G_logic id <- getState;
               b <- parse_basic_spec id;
               return (Basic_spec (G_basic_spec id b))}
  table = [[Prefix (do {string "logic"; spaces;
                        name <- many1 alphaNum;
                        setState (case lookup name logics of
                          Nothing -> error ("logic "++name++" unknown")
                          Just id -> id);
                        spaces; return (\x->x) } )],
           [Postfix (do
             string "with"; spaces;
              do string "logic"; spaces
                 name <- many1 alphaNum
                 G_logic (id::src) <- getState
                 case lookup name translations of
                   Nothing -> error ("translation "++name++" unknown")
                   Just (G_LTR tr) ->
                     case coerce(source tr)::Maybe src of
                       Nothing -> error ("translation type mismatch")
                       Just _ -> do
                         setState (G_logic (target tr))
                         return (\sp -> Inter_Translation sp (G_LTR tr))
              <|> do G_logic id <- getState
                     sy <- parse_symbol_mapping id
                     spaces
                     return (\sp -> Intra_Translation sp (G_symbol_mapping_list id sy))
              )],
           [Infix (do{string "then"; spaces; return Extension}) AssocLeft]
          ]
