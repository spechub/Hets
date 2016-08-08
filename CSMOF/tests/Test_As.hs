{- |
Module      :  ./CSMOF/tests/Test_As.hs
Description :  Test case for the CSMOF abstract structure
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

-- From the CSMOF folder run:  ghc -i.. -o main Test_As.hs

import CSMOF.As
import CSMOF.Print

main :: IO ()
main = let metamodel = Metamodel { metamodelName = "ClassMetamodel"
                                , element = [namedElement_String
                                            , namedElement_UMLModelElement
                                            , namedElement_Attribute
                                            , namedElement_Package
                                            , namedElement_Classifier
                                            , namedElement_Class
                                            , namedElement_PrimitiveDataType
                                            , namedElement_Pkind
                                            , namedElement_Pname
                                            , namedElement_Pnamespace
                                            , namedElement_Pelements
                                            , namedElement_Ptype
                                            , namedElement_Powner
                                            , namedElement_Pattribute
                                            ]
                                , model = [modelM]
                                }
           namedElement_String = NamedElement { namedElementName = "String"
                                              , namedElementOwner = metamodel
                                              , namedElementSubClasses = TType { getType = type_String }
                                              }
           type_String = Type { typeSuper = namedElement_String
                              , typeSubClasses = DDataType { getDataType =
                                                                DataType { classSuper = type_String }
                                                           }
                              }

           namedElement_UMLModelElement = NamedElement { namedElementName = "UMLModelElement"
                                                       , namedElementOwner = metamodel
                                                       , namedElementSubClasses = TType { getType = type_UMLModelElement }
                                                       }
           type_UMLModelElement = Type { typeSuper = namedElement_UMLModelElement
                                       , typeSubClasses = DClass { getClass = class_UMLModelElement }
                                       }
           class_UMLModelElement = Class { classSuperType = type_UMLModelElement
                                         , isAbstract = True
                                         , superClass = []
                                         , ownedAttribute = [property_kind, property_name]
                                         }


           namedElement_Package = NamedElement { namedElementName = "Package"
                                               , namedElementOwner = metamodel
                                               , namedElementSubClasses = TType { getType = type_Package }
                                               }
           type_Package = Type { typeSuper = namedElement_Package
                               , typeSubClasses = DClass { getClass = class_Package }
                               }
           class_Package = Class { classSuperType = type_Package
                                 , isAbstract = False
                                 , superClass = [class_UMLModelElement]
                                 , ownedAttribute = [property_elements]
                                 }


           namedElement_Classifier = NamedElement { namedElementName = "Classifier"
                                                  , namedElementOwner = metamodel
                                                  , namedElementSubClasses = TType { getType = type_Classifier }
                                                  }
           type_Classifier = Type { typeSuper = namedElement_Classifier
                                  , typeSubClasses = DClass { getClass = class_Classifier }
                                  }
           class_Classifier = Class { classSuperType = type_Classifier
                                    , isAbstract = False
                                    , superClass = [class_UMLModelElement]
                                    , ownedAttribute = [property_namespace]
                                    }


           namedElement_Attribute = NamedElement { namedElementName = "Attribute"
                                                 , namedElementOwner = metamodel
                                                 , namedElementSubClasses = TType { getType = type_Attribute }
                                                 }
           type_Attribute = Type { typeSuper = namedElement_Attribute
                                 , typeSubClasses = DClass { getClass = class_Attribute }
                                 }
           class_Attribute = Class { classSuperType = type_Attribute
                                   , isAbstract = False
                                   , superClass = [class_UMLModelElement]
                                   , ownedAttribute = [property_type, property_owner]
                                   }


           namedElement_PrimitiveDataType = NamedElement { namedElementName = "PrimitiveDataType"
                                                         , namedElementOwner = metamodel
                                                         , namedElementSubClasses = TType { getType = type_PrimitiveDataType }
                                                         }
           type_PrimitiveDataType = Type { typeSuper = namedElement_PrimitiveDataType
                                         , typeSubClasses = DClass { getClass = class_PrimitiveDataType }
                                         }
           class_PrimitiveDataType = Class { classSuperType = type_PrimitiveDataType
                                           , isAbstract = False
                                           , superClass = [class_Classifier]
                                           , ownedAttribute = []
                                           }


           namedElement_Class = NamedElement { namedElementName = "Class"
                                             , namedElementOwner = metamodel
                                             , namedElementSubClasses = TType { getType = type_Class }
                                             }
           type_Class = Type { typeSuper = namedElement_Class
                             , typeSubClasses = DClass { getClass = class_Class }
                             }
           class_Class = Class { classSuperType = type_Class
                               , isAbstract = False
                               , superClass = [class_Classifier]
                               , ownedAttribute = [property_attribute]
                               }


           namedElement_Pkind = NamedElement { namedElementName = "kind"
                                               , namedElementOwner = metamodel
                                               , namedElementSubClasses = TTypedElement { getTypeElement = typedElement_kind }
                                               }
           typedElement_kind = TypedElement { typedElementSuper = namedElement_Pkind
                                            , typedElementType = type_String
                                            , typedElementSubClasses = property_kind
                                            }
           property_kind = Property { propertySuper = typedElement_kind
                                    , multiplicityElement = MultiplicityElement { lower = 1
                                                                                , upper = 1
                                                                                , multiplicityElementSubClasses = property_kind
                                                                                }
                                    , opposite = Nothing
                                    , propertyClass = class_UMLModelElement
                                    }


           namedElement_Pname = NamedElement { namedElementName = "name"
                                             , namedElementOwner = metamodel
                                             , namedElementSubClasses = TTypedElement { getTypeElement = typedElement_name }
                                             }
           typedElement_name = TypedElement { typedElementSuper = namedElement_Pname
                                            , typedElementType = type_String
                                            , typedElementSubClasses = property_name
                                            }
           property_name = Property { propertySuper = typedElement_name
                                    , multiplicityElement = MultiplicityElement { lower = 1
                                                                                , upper = 1
                                                                                , multiplicityElementSubClasses = property_name
                                                                                }
                                    , opposite = Nothing
                                    , propertyClass = class_UMLModelElement
                                    }


           namedElement_Pnamespace = NamedElement { namedElementName = "namespace"
                                             , namedElementOwner = metamodel
                                             , namedElementSubClasses = TTypedElement { getTypeElement = typedElement_namespace }
                                             }
           typedElement_namespace = TypedElement { typedElementSuper = namedElement_Pnamespace
                                                 , typedElementType = type_Package
                                                 , typedElementSubClasses = property_namespace
                                                 }
           property_namespace = Property { propertySuper = typedElement_namespace
                                         , multiplicityElement = MultiplicityElement { lower = 1
                                                                                     , upper = 1
                                                                                     , multiplicityElementSubClasses = property_namespace
                                                                                     }
                                         , opposite = Just property_elements
                                         , propertyClass = class_Classifier
                                         }


           namedElement_Pelements = NamedElement { namedElementName = "elements"
                                                 , namedElementOwner = metamodel
                                                 , namedElementSubClasses = TTypedElement { getTypeElement = typedElement_elements }
                                                 }
           typedElement_elements = TypedElement { typedElementSuper = namedElement_Pelements
                                                , typedElementType = type_Classifier
                                                , typedElementSubClasses = property_elements
                                                }
           property_elements = Property { propertySuper = typedElement_elements
                                         , multiplicityElement = MultiplicityElement { lower = 0
                                                                                     , upper = -1
                                                                                     , multiplicityElementSubClasses = property_elements
                                                                                     }
                                         , opposite = Just property_namespace
                                         , propertyClass = class_Package
                                         }


           namedElement_Powner = NamedElement { namedElementName = "owner"
                                             , namedElementOwner = metamodel
                                             , namedElementSubClasses = TTypedElement { getTypeElement = typedElement_owner }
                                             }
           typedElement_owner = TypedElement { typedElementSuper = namedElement_Powner
                                                 , typedElementType = type_Class
                                                 , typedElementSubClasses = property_owner
                                                 }
           property_owner = Property { propertySuper = typedElement_owner
                                         , multiplicityElement = MultiplicityElement { lower = 1
                                                                                     , upper = 1
                                                                                     , multiplicityElementSubClasses = property_owner
                                                                                     }
                                         , opposite = Just property_attribute
                                         , propertyClass = class_Attribute
                                         }


           namedElement_Pattribute = NamedElement { namedElementName = "attribute"
                                             , namedElementOwner = metamodel
                                             , namedElementSubClasses = TTypedElement { getTypeElement = typedElement_attribute }
                                             }
           typedElement_attribute = TypedElement { typedElementSuper = namedElement_Pattribute
                                                 , typedElementType = type_Attribute
                                                 , typedElementSubClasses = property_attribute
                                                 }
           property_attribute = Property { propertySuper = typedElement_attribute
                                         , multiplicityElement = MultiplicityElement { lower = 0
                                                                                     , upper = -1
                                                                                     , multiplicityElementSubClasses = property_attribute
                                                                                     }
                                         , opposite = Just property_owner
                                         , propertyClass = class_Class
                                         }


           namedElement_Ptype = NamedElement { namedElementName = "type"
                                             , namedElementOwner = metamodel
                                             , namedElementSubClasses = TTypedElement { getTypeElement = typedElement_type }
                                             }
           typedElement_type = TypedElement { typedElementSuper = namedElement_Ptype
                                            , typedElementType = type_PrimitiveDataType
                                            , typedElementSubClasses = property_type
                                            }
           property_type = Property { propertySuper = typedElement_type
                                    , multiplicityElement = MultiplicityElement { lower = 1
                                                                                , upper = 1
                                                                                , multiplicityElementSubClasses = property_type
                                                                                }
                                    , opposite = Nothing
                                    , propertyClass = class_Attribute
                                    }


           modelM = Model { modelName = "ClassModel"
                          , object = [object_p
                                     , object_a
                                     , object_c
                                     , object_pdt
                                     , object_Package
                                     , object_ID
                                     , object_Persistent
                                     , object_value
                                     , object_String
                                     , object_EMPTY
                                     ]

                          , link = [link_pc
                                   , link_ca
                                   , link_apdt
                                   , link_pname
                                   , link_pkind
                                   , link_ppdt
                                   , link_aname
                                   , link_cname
                                   , link_pdtname
                                   , link_ckind
                                   , link_akind
                                   , link_pdtkind
                                   ]

                          , modelType = metamodel
                          }

           object_p = Object { objectName = "p"
                             , objectType = type_Package
                             , objectOwner = modelM
                             }
           object_c = Object { objectName = "c"
                             , objectType = type_Class
                             , objectOwner = modelM
                             }
           object_a = Object { objectName = "a"
                             , objectType = type_Attribute
                             , objectOwner = modelM
                             }
           object_pdt = Object { objectName = "pdt"
                               , objectType = type_PrimitiveDataType
                               , objectOwner = modelM
                               }
           object_Package = Object { objectName = "Package"
                                   , objectType = type_String
                                   , objectOwner = modelM
                                   }
           object_ID = Object { objectName = "ID"
                              , objectType = type_String
                              , objectOwner = modelM
                              }
           object_Persistent = Object { objectName = "Persistent"
                                      , objectType = type_String
                                      , objectOwner = modelM
                                      }
           object_value = Object { objectName = "value"
                                 , objectType = type_String
                                 , objectOwner = modelM
                                 }
           object_String = Object { objectName = "String"
                                  , objectType = type_String
                                  , objectOwner = modelM
                                  }
           object_EMPTY = Object { objectName = "EMPTY"
                                 , objectType = type_String
                                 , objectOwner = modelM
                                 }
           link_pc = Link { linkType = property_elements
                          , source = object_p
                          , target = object_c
                          , linkOwner = modelM
                          }
           link_ppdt = Link { linkType = property_elements
                            , source = object_p
                            , target = object_pdt
                            , linkOwner = modelM
                            }
           link_ca = Link { linkType = property_attribute
                          , source = object_c
                          , target = object_a
                          , linkOwner = modelM
                          }
           link_apdt = Link { linkType = property_type
                            , source = object_a
                            , target = object_pdt
                            , linkOwner = modelM
                            }
           link_pname = Link { linkType = property_name
                             , source = object_p
                             , target = object_Package
                             , linkOwner = modelM
                             }
           link_aname = Link { linkType = property_name
                             , source = object_a
                             , target = object_ID
                             , linkOwner = modelM
                             }
           link_cname = Link { linkType = property_name
                             , source = object_c
                             , target = object_value
                             , linkOwner = modelM
                             }
           link_pdtname = Link { linkType = property_name
                               , source = object_pdt
                               , target = object_String
                               , linkOwner = modelM
                               }
           link_pkind = Link { linkType = property_kind
                             , source = object_p
                             , target = object_EMPTY
                             , linkOwner = modelM
                             }
           link_ckind = Link { linkType = property_kind
                             , source = object_c
                             , target = object_Persistent
                             , linkOwner = modelM
                             }
           link_akind = Link { linkType = property_kind
                             , source = object_a
                             , target = object_EMPTY
                             , linkOwner = modelM
                             }
           link_pdtkind = Link { linkType = property_kind
                               , source = object_pdt
                               , target = object_EMPTY
                               , linkOwner = modelM
                               }

        in print metamodel
