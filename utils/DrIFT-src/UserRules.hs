-- stub module to add your own rules.
module UserRules where

import RuleUtils -- gives some examples 

import UserRulesHetCATS

import UserRuleBinary
import UserRuleXml
import UserRulesGeneric

-- add your rules to this list
userRules :: [Rule]
userRules = [("Haskell2Xml", userRuleXml), ("Binary", userRuleBinary)] 
	    ++ userRulesGeneric ++ hetcatsrules 
	    