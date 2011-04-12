thf(con,conjecture,( mvalid @ ( mbox @ fool @ ^ [X: $i] : ! [Z: reg,Y: reg] : ( ( ( p @ Z @ spain ) & ( p @ Y @ france ) ) => ~ ( o @ Z @ Y ) ) ) )).



%thf(t_axiom_for_fool,axiom,( mvalid @ ( mforall_prop @ ^ [A: $i > $o] : ( mimplies @ ( mbox @ fool @ A ) @ A ) ) )).

/*
TPTP_THF_Annotated_Formula {
    ttaf_name = N_Atomic_Word "t_axiom_for_fool",
    ttaf_formula_role = Axiom,
    ttaf_thf_formula = TF_THF_Logic_Formula (
        TLF_THF_Unitary_Formula (
            TUF_THF_Logic_Formula (
                TLF_THF_Binary_Formula (
                    TBF_THF_Binary_Tuple (
                        TBT_THF_Apply_Formula (
                            TApF_THF_Apply_Formula (
                                TUF_THF_atom (
                                    TA_Term (
                                        T_Function_Term (
                                            FT_Plain_Term (
                                                PT_Constant "mvalid"
                                            )
                                        )
                                    )
                                )
                            ) [TUF_THF_Logic_Formula (
                                TLF_THF_Binary_Formula (
                                    TBF_THF_Binary_Tuple (
                                        TBT_THF_Apply_Formula (
                                            TApF_THF_Apply_Formula (
                                                TUF_THF_atom (
                                                    TA_Term (
                                                        T_Function_Term (
                                                            FT_Plain_Term (
                                                                PT_Constant "mforall_prop"
                                                            )
                                                        )
                                                    )
                                                )
                                            ) [TUF_THF_Quantified_Formula
                                                (TQF_THF_Quantified_Formula {
                                                    thf_quantifier = Lambda_Binder,
                                                    thf_variable_list = [TV_THF_Typed_Variable (
                                                        TTV_THF_Typed_Variable {
                                                            ttv_variable = "A",
                                                            ttv_thf_top_level_type = TLF_THF_Binary_Formula (
                                                                TBF_THF_Binary_Type (
                                                                    TBT_THF_Mapping_Type (
                                                                        TMT_THF_Mapping_Type (
                                                                            TUF_THF_atom (
                                                                                TA_Defined_Type DT_i
                                                                            )
                                                                        ) [TUF_THF_atom (
                                                                            TA_Defined_Type DT_o
                                                                        )]
                                                                    )
                                                                )
                                                            )
                                                        }
                                                    )],
                                                    thf_unitary_formula = TUF_THF_Logic_Formula (
                                                        TLF_THF_Binary_Formula (
                                                            TBF_THF_Binary_Tuple (
                                                                TBT_THF_Apply_Formula (
                                                                    TApF_THF_Apply_Formula (
                                                                        TUF_THF_atom (
                                                                            TA_Term (
                                                                                T_Function_Term (
                                                                                    FT_Plain_Term (
                                                                                        PT_Constant "mimplies"
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                    ) [TUF_THF_Logic_Formula (
                                                                        TLF_THF_Binary_Formula (
                                                                            TBF_THF_Binary_Tuple (
                                                                                TBT_THF_Apply_Formula (
                                                                                    TApF_THF_Apply_Formula (
                                                                                        TUF_THF_atom (
                                                                                            TA_Term (
                                                                                                T_Function_Term (
                                                                                                    FT_Plain_Term (
                                                                                                        PT_Constant "mbox"
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    ) [TUF_THF_atom (
                                                                                        TA_Term (
                                                                                            T_Function_Term (
                                                                                                FT_Plain_Term (
                                                                                                    PT_Constant "fool"
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    ),
                                                                                    TUF_THF_atom (
                                                                                        TA_Term (
                                                                                            T_Variable "A"
                                                                                        )
                                                                                    )]
                                                                                )
                                                                            )
                                                                        )
                                                                    ),
                                                                    TUF_THF_atom (
                                                                        TA_Term (
                                                                            T_Variable "A"
                                                                        )
                                                                    )]
                                                                )
                                                            )
                                                        )
                                                    )
                                                }
                                            )]
                                        )
                                    )
                                )
                            )]
                        )
                    )
                )
            )
        )
    ),
    ttaf_annotations = Null
}
*/
