{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZemptyZ45Ztype

-- foundation.decidable-types.is-decidable
d_is'45'decidable_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'decidable_8 = erased
-- foundation.decidable-types.is-decidable-fam
d_is'45'decidable'45'fam_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> ()
d_is'45'decidable'45'fam_20 = erased
-- foundation.decidable-types.is-inhabited-or-empty
d_is'45'inhabited'45'or'45'empty_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'inhabited'45'or'45'empty_30 = erased
-- foundation.decidable-types.is-merely-decidable-Prop
d_is'45'merely'45'decidable'45'Prop_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'merely'45'decidable'45'Prop_36 v0 ~v1
  = du_is'45'merely'45'decidable'45'Prop_36 v0
du_is'45'merely'45'decidable'45'Prop_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'merely'45'decidable'45'Prop_36 v0
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
      v0 erased
-- foundation.decidable-types.is-merely-decidable
d_is'45'merely'45'decidable_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'merely'45'decidable_42 = erased
-- foundation.decidable-types.is-decidable-unit
d_is'45'decidable'45'unit_46 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'unit_46
  = coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
-- foundation.decidable-types.is-decidable-empty
d_is'45'decidable'45'empty_48 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'empty_48
  = coe
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
      (coe (\ v0 -> v0))
-- foundation.decidable-types._.is-decidable-is-left
d_is'45'decidable'45'is'45'left_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'left_64 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'decidable'45'is'45'left_64 v4
du_is'45'decidable'45'is'45'left_64 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'is'45'left_64 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe d_is'45'decidable'45'unit_46
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe d_is'45'decidable'45'empty_48
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types._.is-decidable-is-right
d_is'45'decidable'45'is'45'right_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'right_72 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'decidable'45'is'45'right_72 v4
du_is'45'decidable'45'is'45'right_72 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'is'45'right_72 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe d_is'45'decidable'45'empty_48
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe d_is'45'decidable'45'unit_46
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types.is-decidable-coprod
d_is'45'decidable'45'coprod_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'coprod_86 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_is'45'decidable'45'coprod_86 v4 v5
du_is'45'decidable'45'coprod_86 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'coprod_86 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v0)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                    (coe
                       MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v3))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe
                       MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.du_ind'45'coprod_44
                       (coe v2) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types.is-decidable-prod
d_is'45'decidable'45'prod_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'prod_110 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_is'45'decidable'45'prod_110 v4 v5
du_is'45'decidable'45'prod_110 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'prod_110 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                       (coe v2) (coe v3))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                       (coe (\ v4 -> v3))
                       (coe
                          MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                (coe
                   MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                   (coe (\ v3 -> v2))
                   (coe
                      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types.is-decidable-prod'
d_is'45'decidable'45'prod''_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'prod''_136 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_is'45'decidable'45'prod''_136 v4 v5
du_is'45'decidable'45'prod''_136 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'prod''_136 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> let v3 = coe v1 v2 in
           case coe v3 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                       (coe v2) (coe v4))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                       (coe (\ v5 -> v4))
                       (coe
                          MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                (coe (\ v3 -> v2))
                (coe
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types.is-decidable-function-type
d_is'45'decidable'45'function'45'type_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'function'45'type_170 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_is'45'decidable'45'function'45'type_170 v4 v5
du_is'45'decidable'45'function'45'type_170 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'function'45'type_170 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                    (coe (\ v4 -> v3))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe (\ v4 -> coe v3 (coe v4 v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                (coe
                   MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                   (coe
                      (\ v3 ->
                         coe
                           MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18))
                   (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types.is-decidable-function-type'
d_is'45'decidable'45'function'45'type''_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'function'45'type''_200 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_is'45'decidable'45'function'45'type''_200 v4 v5
du_is'45'decidable'45'function'45'type''_200 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  (AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'function'45'type''_200 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> let v3 = coe v1 v2 in
           case coe v3 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                    (coe (\ v5 -> v4))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe (\ v5 -> coe v4 (coe v5 v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                (coe
                   (\ v3 ->
                      coe
                        MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18))
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types.is-decidable-neg
d_is'45'decidable'45'neg_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'neg_234 ~v0 ~v1 v2
  = du_is'45'decidable'45'neg_234 v2
du_is'45'decidable'45'neg_234 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'neg_234 v0
  = coe
      du_is'45'decidable'45'function'45'type_170 (coe v0)
      (coe d_is'45'decidable'45'empty_48)
-- foundation.decidable-types._.is-decidable-iff
d_is'45'decidable'45'iff_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'iff_250 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_is'45'decidable'45'iff_250 v4 v5 v6
du_is'45'decidable'45'iff_250 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'iff_250 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v0 v3)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
             (coe (\ v4 -> coe v3 (coe v1 v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types._.is-decidable-retract-of
d_is'45'decidable'45'retract'45'of_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'retract'45'of_278 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_is'45'decidable'45'retract'45'of_278 v4 v5
du_is'45'decidable'45'retract'45'of_278 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'retract'45'of_278 v0 v1
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> case coe v3 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
               -> case coe v1 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v6
                      -> coe
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v4 v6)
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v6
                      -> coe
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                           (coe
                              MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                              (coe (\ v7 -> v6)) (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types._.is-decidable-is-equiv
d_is'45'decidable'45'is'45'equiv_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'equiv_298 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_is'45'decidable'45'is'45'equiv_298 v4 v5
du_is'45'decidable'45'is'45'equiv_298 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'is'45'equiv_298 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> coe
             seq (coe v2)
             (coe
                seq (coe v3)
                (coe
                   du_is'45'decidable'45'retract'45'of_278
                   (coe
                      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                      (coe v0) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types._.is-decidable-equiv
d_is'45'decidable'45'equiv_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'equiv_312 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'decidable'45'equiv_312 v4
du_is'45'decidable'45'equiv_312 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'equiv_312 v0
  = coe
      du_is'45'decidable'45'iff_250
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'equiv_240
         (coe v0))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
         (coe v0))
-- foundation.decidable-types.is-decidable-equiv'
d_is'45'decidable'45'equiv''_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'equiv''_326 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'decidable'45'equiv''_326 v4
du_is'45'decidable'45'equiv''_326 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'equiv''_326 v0
  = coe
      du_is'45'decidable'45'equiv_312
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
         (coe v0))
-- foundation.decidable-types.dn-elim-is-decidable
d_dn'45'elim'45'is'45'decidable_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  ((AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny
d_dn'45'elim'45'is'45'decidable_334 ~v0 ~v1 v2 ~v3
  = du_dn'45'elim'45'is'45'decidable_334 v2
du_dn'45'elim'45'is'45'decidable_334 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
du_dn'45'elim'45'is'45'decidable_334 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1 -> coe v1
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types.dn-is-decidable
d_dn'45'is'45'decidable_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_dn'45'is'45'decidable_352 = erased
-- foundation.decidable-types.idempotent-is-decidable
d_idempotent'45'is'45'decidable_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_idempotent'45'is'45'decidable_362 ~v0 ~v1 v2
  = du_idempotent'45'is'45'decidable_362 v2
du_idempotent'45'is'45'decidable_362 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_idempotent'45'is'45'decidable_362 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1 -> coe v1
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
             (coe
                (\ v2 ->
                   coe
                     v1
                     (coe
                        MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types.is-prop-is-inhabited-or-empty
d_is'45'prop'45'is'45'inhabited'45'or'45'empty_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'inhabited'45'or'45'empty_382 ~v0 ~v1
  = du_is'45'prop'45'is'45'inhabited'45'or'45'empty_382
du_is'45'prop'45'is'45'inhabited'45'or'45'empty_382 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'inhabited'45'or'45'empty_382
  = coe
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.du_is'45'prop'45'coprod_264
-- foundation.decidable-types.is-inhabited-or-empty-Prop
d_is'45'inhabited'45'or'45'empty'45'Prop_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'inhabited'45'or'45'empty'45'Prop_390 ~v0 ~v1
  = du_is'45'inhabited'45'or'45'empty'45'Prop_390
du_is'45'inhabited'45'or'45'empty'45'Prop_390 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'inhabited'45'or'45'empty'45'Prop_390
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'is'45'inhabited'45'or'45'empty_382)
-- foundation.decidable-types.is-prop-is-decidable
d_is'45'prop'45'is'45'decidable_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'decidable_400 ~v0 ~v1 ~v2
  = du_is'45'prop'45'is'45'decidable_400
du_is'45'prop'45'is'45'decidable_400 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'decidable_400
  = coe
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.du_is'45'prop'45'coprod_264
-- foundation.decidable-types.is-decidable-Prop
d_is'45'decidable'45'Prop_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'decidable'45'Prop_406 ~v0 ~v1
  = du_is'45'decidable'45'Prop_406
du_is'45'decidable'45'Prop_406 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'decidable'45'Prop_406
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'is'45'decidable_400)
-- foundation.decidable-types.is-prop-is-decidable-trunc-Prop
d_is'45'prop'45'is'45'decidable'45'trunc'45'Prop_416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'decidable'45'trunc'45'Prop_416 ~v0 ~v1
  = du_is'45'prop'45'is'45'decidable'45'trunc'45'Prop_416
du_is'45'prop'45'is'45'decidable'45'trunc'45'Prop_416 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'decidable'45'trunc'45'Prop_416
  = coe du_is'45'prop'45'is'45'decidable_400
-- foundation.decidable-types.is-decidable-trunc-Prop
d_is'45'decidable'45'trunc'45'Prop_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'decidable'45'trunc'45'Prop_422 ~v0 ~v1
  = du_is'45'decidable'45'trunc'45'Prop_422
du_is'45'decidable'45'trunc'45'Prop_422 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'decidable'45'trunc'45'Prop_422
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'is'45'decidable'45'trunc'45'Prop_416)
-- foundation.decidable-types.is-decidable-trunc-Prop-is-merely-decidable
d_is'45'decidable'45'trunc'45'Prop'45'is'45'merely'45'decidable_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'trunc'45'Prop'45'is'45'merely'45'decidable_432 v0
                                                                    ~v1
  = du_is'45'decidable'45'trunc'45'Prop'45'is'45'merely'45'decidable_432
      v0
du_is'45'decidable'45'trunc'45'Prop'45'is'45'merely'45'decidable_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'trunc'45'Prop'45'is'45'merely'45'decidable_432 v0
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_map'45'universal'45'property'45'trunc'45'Prop_176
      (coe v0) (coe v0) (coe du_is'45'decidable'45'trunc'45'Prop_422)
      (coe du_f_440 (coe v0))
-- foundation.decidable-types._.f
d_f_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_f_440 v0 ~v1 v2 = du_f_440 v0 v2
du_f_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_f_440 v0 v1
  = case coe v1 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
             (coe
                MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
                v0 v2)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
             (coe
                MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_map'45'universal'45'property'45'trunc'45'Prop_176
                (coe v0) (coe ())
                (coe
                   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.d_empty'45'Prop_90)
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types.is-merely-decidable-is-decidable-trunc-Prop
d_is'45'merely'45'decidable'45'is'45'decidable'45'trunc'45'Prop_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_is'45'merely'45'decidable'45'is'45'decidable'45'trunc'45'Prop_450 v0
                                                                    ~v1 v2
  = du_is'45'merely'45'decidable'45'is'45'decidable'45'trunc'45'Prop_450
      v0 v2
du_is'45'merely'45'decidable'45'is'45'decidable'45'trunc'45'Prop_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
du_is'45'merely'45'decidable'45'is'45'decidable'45'trunc'45'Prop_450 v0
                                                                     v1
  = case coe v1 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> coe
             MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
             (coe v0) (coe v0) (coe v2)
             (coe du_is'45'merely'45'decidable'45'Prop_36 (coe v0))
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                (coe
                   (\ v3 ->
                      coe
                        MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
                        (coe v0)))
                (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22))
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> coe
             MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
             v0
             (coe
                MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                (coe
                   MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                   (coe (\ v3 -> v2))
                   (coe
                      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
                      (coe v0))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-types.is-fixed-point-is-decidable-is-inhabited
d_is'45'fixed'45'point'45'is'45'decidable'45'is'45'inhabited_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'fixed'45'point'45'is'45'decidable'45'is'45'inhabited_464 ~v0
                                                                 ~v1 ~v2
  = du_is'45'fixed'45'point'45'is'45'decidable'45'is'45'inhabited_464
du_is'45'fixed'45'point'45'is'45'decidable'45'is'45'inhabited_464 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'fixed'45'point'45'is'45'decidable'45'is'45'inhabited_464
  = coe
      MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZemptyZ45Ztype.du_right'45'unit'45'law'45'coprod'45'is'45'empty_260
-- foundation.decidable-types._.is-decidable-raise
d_is'45'decidable'45'raise_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'raise_482 ~v0 ~v1 ~v2 v3
  = du_is'45'decidable'45'raise_482 v3
du_is'45'decidable'45'raise_482 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'raise_482 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
             (coe
                MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.C_map'45'raise_18
                (coe v1))
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
             (coe
                (\ v2 ->
                   coe
                     v1
                     (MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.d_map'45'inv'45'raise_30
                        (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
