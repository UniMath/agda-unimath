{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- foundation.coproduct-types.coprod
d_coprod_12 a0 a1 a2 a3 = ()
data T_coprod_12 = C_inl_22 AgdaAny | C_inr_24 AgdaAny
-- foundation.coproduct-types.ind-coprod
d_ind'45'coprod_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (T_coprod_12 -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_coprod_12 -> AgdaAny
d_ind'45'coprod_44 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_ind'45'coprod_44 v6 v7 v8
du_ind'45'coprod_44 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_coprod_12 -> AgdaAny
du_ind'45'coprod_44 v0 v1 v2
  = case coe v2 of
      C_inl_22 v3 -> coe v0 v3
      C_inr_24 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.coproduct-types._.is-left-Prop
d_is'45'left'45'Prop_74 ::
  T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'left'45'Prop_74 v0
  = case coe v0 of
      C_inl_22 v1
        -> coe MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_unit'45'Prop_84
      C_inr_24 v1
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.d_empty'45'Prop_90
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.coproduct-types._.is-left
d_is'45'left_80 :: T_coprod_12 -> ()
d_is'45'left_80 = erased
-- foundation.coproduct-types._.is-right-Prop
d_is'45'right'45'Prop_84 ::
  T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'right'45'Prop_84 v0
  = case coe v0 of
      C_inl_22 v1
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.d_empty'45'Prop_90
      C_inr_24 v1
        -> coe MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_unit'45'Prop_84
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.coproduct-types._.is-right
d_is'45'right_90 :: T_coprod_12 -> ()
d_is'45'right_90 = erased
-- foundation.coproduct-types._.is-injective-inl
d_is'45'injective'45'inl_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'inl_106 = erased
-- foundation.coproduct-types._.is-injective-inr
d_is'45'injective'45'inr_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'inr_108 = erased
-- foundation.coproduct-types._.neq-inl-inr
d_neq'45'inl'45'inr_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_neq'45'inl'45'inr_114 = erased
-- foundation.coproduct-types._.neq-inr-inl
d_neq'45'inr'45'inl_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_neq'45'inr'45'inl_120 = erased
-- foundation.coproduct-types._.map-equiv-left-summand
d_map'45'equiv'45'left'45'summand_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_map'45'equiv'45'left'45'summand_134 ~v0 ~v1 ~v2 ~v3 v4
  = du_map'45'equiv'45'left'45'summand_134 v4
du_map'45'equiv'45'left'45'summand_134 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_map'45'equiv'45'left'45'summand_134 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v1 of
             C_inl_22 v3 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.coproduct-types._.map-inv-equiv-left-summand
d_map'45'inv'45'equiv'45'left'45'summand_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'equiv'45'left'45'summand_140 ~v0 ~v1 ~v2 ~v3 v4
  = du_map'45'inv'45'equiv'45'left'45'summand_140 v4
du_map'45'inv'45'equiv'45'left'45'summand_140 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'equiv'45'left'45'summand_140 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe C_inl_22 (coe v0)) erased
-- foundation.coproduct-types._.issec-map-inv-equiv-left-summand
d_issec'45'map'45'inv'45'equiv'45'left'45'summand_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'equiv'45'left'45'summand_144 = erased
-- foundation.coproduct-types._.isretr-map-inv-equiv-left-summand
d_isretr'45'map'45'inv'45'equiv'45'left'45'summand_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'equiv'45'left'45'summand_148 = erased
-- foundation.coproduct-types._.equiv-left-summand
d_equiv'45'left'45'summand_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'left'45'summand_154 ~v0 ~v1 ~v2 ~v3
  = du_equiv'45'left'45'summand_154
du_equiv'45'left'45'summand_154 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'left'45'summand_154
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'equiv'45'left'45'summand_134)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
         (coe du_map'45'inv'45'equiv'45'left'45'summand_140) erased erased)
-- foundation.coproduct-types._.map-equiv-right-summand
d_map'45'equiv'45'right'45'summand_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_map'45'equiv'45'right'45'summand_168 ~v0 ~v1 ~v2 ~v3 v4
  = du_map'45'equiv'45'right'45'summand_168 v4
du_map'45'equiv'45'right'45'summand_168 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_map'45'equiv'45'right'45'summand_168 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v1 of
             C_inr_24 v3 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.coproduct-types._.map-inv-equiv-right-summand
d_map'45'inv'45'equiv'45'right'45'summand_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'equiv'45'right'45'summand_174 ~v0 ~v1 ~v2 ~v3 v4
  = du_map'45'inv'45'equiv'45'right'45'summand_174 v4
du_map'45'inv'45'equiv'45'right'45'summand_174 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'equiv'45'right'45'summand_174 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe C_inr_24 (coe v0)) erased
-- foundation.coproduct-types._.issec-map-inv-equiv-right-summand
d_issec'45'map'45'inv'45'equiv'45'right'45'summand_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'equiv'45'right'45'summand_178 = erased
-- foundation.coproduct-types._.isretr-map-inv-equiv-right-summand
d_isretr'45'map'45'inv'45'equiv'45'right'45'summand_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'equiv'45'right'45'summand_182 = erased
-- foundation.coproduct-types._.equiv-right-summand
d_equiv'45'right'45'summand_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'right'45'summand_188 ~v0 ~v1 ~v2 ~v3
  = du_equiv'45'right'45'summand_188
du_equiv'45'right'45'summand_188 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'right'45'summand_188
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'equiv'45'right'45'summand_168)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
         (coe du_map'45'inv'45'equiv'45'right'45'summand_174) erased erased)
-- foundation.coproduct-types._.is-not-contractible-coprod-is-contr
d_is'45'not'45'contractible'45'coprod'45'is'45'contr_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'not'45'contractible'45'coprod'45'is'45'contr_202 = erased
-- foundation.coproduct-types._.all-elements-equal-coprod
d_all'45'elements'45'equal'45'coprod_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  T_coprod_12 ->
  T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_all'45'elements'45'equal'45'coprod_222 = erased
-- foundation.coproduct-types._.is-prop-coprod
d_is'45'prop'45'coprod_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  T_coprod_12 ->
  T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'coprod_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_is'45'prop'45'coprod_264
du_is'45'prop'45'coprod_264 ::
  T_coprod_12 ->
  T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'coprod_264 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'all'45'elements'45'equal_70
-- foundation.coproduct-types.coprod-Prop
d_coprod'45'Prop_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_coprod'45'Prop_280 ~v0 ~v1 ~v2 ~v3 ~v4 = du_coprod'45'Prop_280
du_coprod'45'Prop_280 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_coprod'45'Prop_280
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'coprod_264)
