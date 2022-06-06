{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QdecidableZ45Zpropositions where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qbooleans
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QemptyZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- foundation.decidable-propositions.is-decidable-prop
d_is'45'decidable'45'prop_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'decidable'45'prop_6 = erased
-- foundation.decidable-propositions.decidable-Prop
d_decidable'45'Prop_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_decidable'45'Prop_12 = erased
-- foundation.decidable-propositions._.prop-decidable-Prop
d_prop'45'decidable'45'Prop_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_prop'45'decidable'45'Prop_24 ~v0 v1
  = du_prop'45'decidable'45'Prop_24 v1
du_prop'45'decidable'45'Prop_24 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_prop'45'decidable'45'Prop_24 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe v0))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
            (coe v0)))
-- foundation.decidable-propositions._.type-decidable-Prop
d_type'45'decidable'45'Prop_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'decidable'45'Prop_26 = erased
-- foundation.decidable-propositions._.is-prop-type-decidable-Prop
d_is'45'prop'45'type'45'decidable'45'Prop_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'type'45'decidable'45'Prop_28 ~v0 v1
  = du_is'45'prop'45'type'45'decidable'45'Prop_28 v1
du_is'45'prop'45'type'45'decidable'45'Prop_28 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'type'45'decidable'45'Prop_28 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
      (coe du_prop'45'decidable'45'Prop_24 (coe v0))
-- foundation.decidable-propositions._.is-decidable-type-decidable-Prop
d_is'45'decidable'45'type'45'decidable'45'Prop_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'type'45'decidable'45'Prop_30 ~v0 v1
  = du_is'45'decidable'45'type'45'decidable'45'Prop_30 v1
du_is'45'decidable'45'type'45'decidable'45'Prop_30 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'type'45'decidable'45'Prop_30 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
         (coe v0))
-- foundation.decidable-propositions._.is-decidable-prop-type-decidable-Prop
d_is'45'decidable'45'prop'45'type'45'decidable'45'Prop_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'decidable'45'prop'45'type'45'decidable'45'Prop_32 ~v0 v1
  = du_is'45'decidable'45'prop'45'type'45'decidable'45'Prop_32 v1
du_is'45'decidable'45'prop'45'type'45'decidable'45'Prop_32 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'decidable'45'prop'45'type'45'decidable'45'Prop_32 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe v0)
-- foundation.decidable-propositions._.is-decidable-prop-decidable-Prop
d_is'45'decidable'45'prop'45'decidable'45'Prop_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'decidable'45'prop'45'decidable'45'Prop_34 ~v0 ~v1
  = du_is'45'decidable'45'prop'45'decidable'45'Prop_34
du_is'45'decidable'45'prop'45'decidable'45'Prop_34 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'decidable'45'prop'45'decidable'45'Prop_34
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'prop'45'is'45'decidable_400)
-- foundation.decidable-propositions.is-prop-is-decidable-prop
d_is'45'prop'45'is'45'decidable'45'prop_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'decidable'45'prop_40 v0 ~v1
  = du_is'45'prop'45'is'45'decidable'45'prop_40 v0
du_is'45'prop'45'is'45'decidable'45'prop_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'decidable'45'prop_40 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'is'45'inhabited_38
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'prod_280
              (coe
                 MAlonzo.Code.Qfoundation.Qpropositions.d_is'45'prop'45'is'45'prop_24
                 v0 erased)
              (coe
                 MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'prop'45'is'45'decidable_400)))
-- foundation.decidable-propositions._.split-decidable-Prop
d_split'45'decidable'45'Prop_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_split'45'decidable'45'Prop_54 ~v0
  = du_split'45'decidable'45'Prop_54
du_split'45'decidable'45'Prop_54 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_split'45'decidable'45'Prop_54
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZcoproductZ45Ztypes.du_left'45'distributive'45'Σ'45'coprod_250)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_inv'45'assoc'45'Σ_166)
-- foundation.decidable-propositions._.map-equiv-bool-decidable-Prop'
d_map'45'equiv'45'bool'45'decidable'45'Prop''_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> Bool
d_map'45'equiv'45'bool'45'decidable'45'Prop''_64 ~v0 v1
  = du_map'45'equiv'45'bool'45'decidable'45'Prop''_64 v1
du_map'45'equiv'45'bool'45'decidable'45'Prop''_64 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> Bool
du_map'45'equiv'45'bool'45'decidable'45'Prop''_64 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe MAlonzo.Code.Qfoundation.Qbooleans.C_true_6
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe MAlonzo.Code.Qfoundation.Qbooleans.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.decidable-propositions._.map-inv-equiv-bool-decidable-Prop'
d_map'45'inv'45'equiv'45'bool'45'decidable'45'Prop''_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Bool -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'inv'45'equiv'45'bool'45'decidable'45'Prop''_72 ~v0 v1
  = du_map'45'inv'45'equiv'45'bool'45'decidable'45'Prop''_72 v1
du_map'45'inv'45'equiv'45'bool'45'decidable'45'Prop''_72 ::
  Bool -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'inv'45'equiv'45'bool'45'decidable'45'Prop''_72 v0
  = if coe v0
      then coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                (coe
                   MAlonzo.Code.Qfoundation.QunitZ45Ztype.du_raise'45'unit'45'Prop_104)
                (coe MAlonzo.Code.Qfoundation.QunitZ45Ztype.du_raise'45'star_34))
      else coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                (coe
                   MAlonzo.Code.Qfoundation.QemptyZ45Ztypes.du_raise'45'empty'45'Prop_76)
                erased)
-- foundation.decidable-propositions._.issec-map-inv-equiv-bool-decidable-Prop'
d_issec'45'map'45'inv'45'equiv'45'bool'45'decidable'45'Prop''_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Bool -> MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'equiv'45'bool'45'decidable'45'Prop''_74
  = erased
-- foundation.decidable-propositions._.isretr-map-inv-equiv-bool-decidable-Prop'
d_isretr'45'map'45'inv'45'equiv'45'bool'45'decidable'45'Prop''_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'equiv'45'bool'45'decidable'45'Prop''_76
  = erased
-- foundation.decidable-propositions._.is-equiv-map-equiv-bool-decidable-Prop'
d_is'45'equiv'45'map'45'equiv'45'bool'45'decidable'45'Prop''_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'equiv'45'bool'45'decidable'45'Prop''_82 ~v0
  = du_is'45'equiv'45'map'45'equiv'45'bool'45'decidable'45'Prop''_82
du_is'45'equiv'45'map'45'equiv'45'bool'45'decidable'45'Prop''_82 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'equiv'45'bool'45'decidable'45'Prop''_82
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'equiv'45'bool'45'decidable'45'Prop''_72)
      erased erased
-- foundation.decidable-propositions._.equiv-bool-decidable-Prop'
d_equiv'45'bool'45'decidable'45'Prop''_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'bool'45'decidable'45'Prop''_86 ~v0
  = du_equiv'45'bool'45'decidable'45'Prop''_86
du_equiv'45'bool'45'decidable'45'Prop''_86 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'bool'45'decidable'45'Prop''_86
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'equiv'45'bool'45'decidable'45'Prop''_64)
      (coe
         du_is'45'equiv'45'map'45'equiv'45'bool'45'decidable'45'Prop''_82)
-- foundation.decidable-propositions._.equiv-bool-decidable-Prop
d_equiv'45'bool'45'decidable'45'Prop_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'bool'45'decidable'45'Prop_88 ~v0
  = du_equiv'45'bool'45'decidable'45'Prop_88
du_equiv'45'bool'45'decidable'45'Prop_88 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'bool'45'decidable'45'Prop_88
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe du_equiv'45'bool'45'decidable'45'Prop''_86)
      (coe du_split'45'decidable'45'Prop_54)
-- foundation.decidable-propositions._.compute-equiv-bool-decidable-Prop
d_compute'45'equiv'45'bool'45'decidable'45'Prop_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_compute'45'equiv'45'bool'45'decidable'45'Prop_92 ~v0 v1
  = du_compute'45'equiv'45'bool'45'decidable'45'Prop_92 v1
du_compute'45'equiv'45'bool'45'decidable'45'Prop_92 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_compute'45'equiv'45'bool'45'decidable'45'Prop_92 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v2 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
                      -> coe
                           MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_equiv'45'is'45'contr_250
                           (coe
                              MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
                              v3 v5)
                           (coe
                              MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
                              (coe
                                 MAlonzo.Code.Qfoundation.Qbooleans.d_is'45'set'45'bool_44
                                 (coe MAlonzo.Code.Qfoundation.Qbooleans.C_true_6)
                                 (coe MAlonzo.Code.Qfoundation.Qbooleans.C_true_6))
                              erased)
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
                      -> coe
                           MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_equiv'45'is'45'empty_82
                           erased erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
