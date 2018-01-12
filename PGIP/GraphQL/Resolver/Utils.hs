module PGIP.GraphQL.Resolver.Utils where

import PGIP.GraphQL.Result.Symbol as GraphQLResultSymbol
import PGIP.GraphQL.Result.FileRange as GraphQLResultFileRange

import Persistence.Schema as DatabaseSchema

import qualified Data.Text as Text
import Database.Esqueleto

symbolEntityToSymbolResult :: ( Entity DatabaseSchema.LocIdBase
                              , Entity DatabaseSchema.Symbol
                              , Maybe (Entity DatabaseSchema.FileRange)
                              )
                           -> GraphQLResultSymbol.Symbol
symbolEntityToSymbolResult (Entity _ locIdBaseValue, Entity _ symbolValue, fileRangeM) =
  let fileRangeResult =
        fmap (\(Entity _ fileRangeValue) -> GraphQLResultFileRange.FileRange
               { GraphQLResultFileRange.startLine = fileRangeStartLine fileRangeValue
               , GraphQLResultFileRange.startColumn = fileRangeStartColumn fileRangeValue
               , GraphQLResultFileRange.endLine = fileRangeEndLine fileRangeValue
               , GraphQLResultFileRange.endColumn = fileRangeEndColumn fileRangeValue
               , GraphQLResultFileRange.path = fileRangePath fileRangeValue
               }) fileRangeM
  in  GraphQLResultSymbol.Symbol
        { GraphQLResultSymbol.__typename = "Symbol"
        , GraphQLResultSymbol.fileRange = fileRangeResult
        , GraphQLResultSymbol.fullName = Text.unpack $ symbolFullName symbolValue
        , GraphQLResultSymbol.kind = symbolSymbolKind symbolValue
        , GraphQLResultSymbol.locId = locIdBaseLocId locIdBaseValue
        , GraphQLResultSymbol.name = symbolName symbolValue
        }
