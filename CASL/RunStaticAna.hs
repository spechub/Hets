{- |
Module      :  $Header$
Description :  make static analysis checkable by RunParsers
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

Make static analysis checkable by RunParsers

-}

module CASL.RunStaticAna where

import Common.AnnoState
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Result
import Common.DocUtils
import Common.ExtSign
import CASL.Parse_AS_Basic
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.StaticAna
import CASL.SimplifySen
import CASL.Quantification
import CASL.AlphaConvert

localAnalysis :: GlobalAnnos -> BASIC_SPEC () () ()
              -> Result (BASIC_SPEC () () ())
localAnalysis ga bs =
        let Result ds ms = basicCASLAnalysis (bs, emptySign () , ga)
        in Result ds $ case ms of
           Just (newBs, _accSig, _sents) -> Just newBs
           _ -> Nothing

runAna :: GlobalAnnos -> AParser () (Result (BASIC_SPEC () () ()))
runAna ga =
    do b <- basicSpec []
       return $ localAnalysis ga b

localAna :: GlobalAnnos -> BASIC_SPEC () () () -> Result (Sign () ())
localAna ga bs =
    let Result ds ms =
            basicCASLAnalysis (bs, emptySign () , ga)
        es = filter ((<= Error)  . diagKind) ds
        in case ms of
           Just (_newBs, ExtSign accSig _, _sents) -> Result es $ Just accSig
           Nothing -> Result ds Nothing

getSign :: GlobalAnnos -> AParser () (Result (Sign () ()))
getSign ga =
    do b <- basicSpec []
       return $ localAna ga b

props :: GlobalAnnos -> BASIC_SPEC () () ()
      -> Result (Sign () (), [Named (FORMULA ())])
props ga bs =
    let Result ds ms =
            basicCASLAnalysis (bs, emptySign (), ga)
        in Result ds $ case ms of
           Just (_newBs, ExtSign accSig _, sents) -> Just (accSig,
                     map (mapNamed $ simplifySen (error "props1")
                                     (error "props2") accSig
                           . stripQuant accSig . convertFormula 1 id)
                       sents)
           Nothing -> Nothing

getProps :: GlobalAnnos
         -> AParser () (Result (Sign () (), [Annoted (FORMULA ())]))
getProps ga =
    do b <- basicSpec []
       return $ fmap ( \ (sign, sens) -> (sign, map fromLabelledSen sens))
              $ props ga b
