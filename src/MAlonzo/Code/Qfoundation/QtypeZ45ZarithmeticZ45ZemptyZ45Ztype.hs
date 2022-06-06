{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZemptyZ45Ztype where

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
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes

-- foundation.type-arithmetic-empty-type._.inv-pr1-prod-empty
d_inv'45'pr1'45'prod'45'empty_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'pr1'45'prod'45'empty_12 ~v0 ~v1 ~v2
  = du_inv'45'pr1'45'prod'45'empty_12
du_inv'45'pr1'45'prod'45'empty_12 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'pr1'45'prod'45'empty_12 = MAlonzo.RTE.mazUnreachableError
-- foundation.type-arithmetic-empty-type._.issec-inv-pr1-prod-empty
d_issec'45'inv'45'pr1'45'prod'45'empty_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'inv'45'pr1'45'prod'45'empty_14 = erased
-- foundation.type-arithmetic-empty-type._.isretr-inv-pr1-prod-empty
d_isretr'45'inv'45'pr1'45'prod'45'empty_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'inv'45'pr1'45'prod'45'empty_16 = erased
-- foundation.type-arithmetic-empty-type._.is-equiv-pr1-prod-empty
d_is'45'equiv'45'pr1'45'prod'45'empty_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'pr1'45'prod'45'empty_22 ~v0 ~v1
  = du_is'45'equiv'45'pr1'45'prod'45'empty_22
du_is'45'equiv'45'pr1'45'prod'45'empty_22 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'pr1'45'prod'45'empty_22
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (\ v0 -> coe du_inv'45'pr1'45'prod'45'empty_12) erased erased
-- foundation.type-arithmetic-empty-type._.left-zero-law-prod
d_left'45'zero'45'law'45'prod_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_left'45'zero'45'law'45'prod_24 ~v0 ~v1
  = du_left'45'zero'45'law'45'prod_24
du_left'45'zero'45'law'45'prod_24 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_left'45'zero'45'law'45'prod_24
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26)
      (coe du_is'45'equiv'45'pr1'45'prod'45'empty_22)
-- foundation.type-arithmetic-empty-type._.inv-pr2-prod-empty
d_inv'45'pr2'45'prod'45'empty_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'pr2'45'prod'45'empty_34 ~v0 ~v1 ~v2
  = du_inv'45'pr2'45'prod'45'empty_34
du_inv'45'pr2'45'prod'45'empty_34 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'pr2'45'prod'45'empty_34 = MAlonzo.RTE.mazUnreachableError
-- foundation.type-arithmetic-empty-type._.issec-inv-pr2-prod-empty
d_issec'45'inv'45'pr2'45'prod'45'empty_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'inv'45'pr2'45'prod'45'empty_36 = erased
-- foundation.type-arithmetic-empty-type._.isretr-inv-pr2-prod-empty
d_isretr'45'inv'45'pr2'45'prod'45'empty_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'inv'45'pr2'45'prod'45'empty_38 = erased
-- foundation.type-arithmetic-empty-type._.is-equiv-pr2-prod-empty
d_is'45'equiv'45'pr2'45'prod'45'empty_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'pr2'45'prod'45'empty_44 ~v0 ~v1
  = du_is'45'equiv'45'pr2'45'prod'45'empty_44
du_is'45'equiv'45'pr2'45'prod'45'empty_44 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'pr2'45'prod'45'empty_44
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (\ v0 -> coe du_inv'45'pr2'45'prod'45'empty_34) erased erased
-- foundation.type-arithmetic-empty-type._.right-zero-law-prod
d_right'45'zero'45'law'45'prod_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_right'45'zero'45'law'45'prod_46 ~v0 ~v1
  = du_right'45'zero'45'law'45'prod_46
du_right'45'zero'45'law'45'prod_46 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_right'45'zero'45'law'45'prod_46
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28)
      (coe du_is'45'equiv'45'pr2'45'prod'45'empty_44)
-- foundation.type-arithmetic-empty-type._.map-right-absorption-Σ
d_map'45'right'45'absorption'45'Σ_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_map'45'right'45'absorption'45'Σ_58 = erased
-- foundation.type-arithmetic-empty-type._.is-equiv-map-right-absorption-Σ
d_is'45'equiv'45'map'45'right'45'absorption'45'Σ_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'right'45'absorption'45'Σ_62 ~v0 ~v1
  = du_is'45'equiv'45'map'45'right'45'absorption'45'Σ_62
du_is'45'equiv'45'map'45'right'45'absorption'45'Σ_62 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'right'45'absorption'45'Σ_62
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'equiv'45'is'45'empty''_70
-- foundation.type-arithmetic-empty-type._.right-absorption-Σ
d_right'45'absorption'45'Σ_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_right'45'absorption'45'Σ_66 ~v0 ~v1
  = du_right'45'absorption'45'Σ_66
du_right'45'absorption'45'Σ_66 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_right'45'absorption'45'Σ_66
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'equiv'45'map'45'right'45'absorption'45'Σ_62)
-- foundation.type-arithmetic-empty-type._.map-left-absorption-Σ
d_map'45'left'45'absorption'45'Σ_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_map'45'left'45'absorption'45'Σ_76 = erased
-- foundation.type-arithmetic-empty-type._.is-equiv-map-left-absorption-Σ
d_is'45'equiv'45'map'45'left'45'absorption'45'Σ_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'left'45'absorption'45'Σ_78 ~v0 ~v1
  = du_is'45'equiv'45'map'45'left'45'absorption'45'Σ_78
du_is'45'equiv'45'map'45'left'45'absorption'45'Σ_78 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'left'45'absorption'45'Σ_78
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'equiv'45'is'45'empty''_70
-- foundation.type-arithmetic-empty-type._.left-absorption-Σ
d_left'45'absorption'45'Σ_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_left'45'absorption'45'Σ_80 ~v0 ~v1
  = du_left'45'absorption'45'Σ_80
du_left'45'absorption'45'Σ_80 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_left'45'absorption'45'Σ_80
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'equiv'45'map'45'left'45'absorption'45'Σ_78)
-- foundation.type-arithmetic-empty-type._.map-right-absorption-prod
d_map'45'right'45'absorption'45'prod_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_map'45'right'45'absorption'45'prod_90 = erased
-- foundation.type-arithmetic-empty-type._.is-equiv-map-right-absorption-prod
d_is'45'equiv'45'map'45'right'45'absorption'45'prod_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'right'45'absorption'45'prod_92 ~v0 ~v1
  = du_is'45'equiv'45'map'45'right'45'absorption'45'prod_92
du_is'45'equiv'45'map'45'right'45'absorption'45'prod_92 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'right'45'absorption'45'prod_92
  = coe du_is'45'equiv'45'map'45'right'45'absorption'45'Σ_62
-- foundation.type-arithmetic-empty-type._.right-absorption-prod
d_right'45'absorption'45'prod_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_right'45'absorption'45'prod_94 ~v0 ~v1
  = du_right'45'absorption'45'prod_94
du_right'45'absorption'45'prod_94 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_right'45'absorption'45'prod_94
  = coe du_right'45'absorption'45'Σ_66
-- foundation.type-arithmetic-empty-type.is-empty-right-factor-is-empty-prod
d_is'45'empty'45'right'45'factor'45'is'45'empty'45'prod_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'right'45'factor'45'is'45'empty'45'prod_104
  = erased
-- foundation.type-arithmetic-empty-type._.map-left-absorption-prod
d_map'45'left'45'absorption'45'prod_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_map'45'left'45'absorption'45'prod_120 = erased
-- foundation.type-arithmetic-empty-type._.is-equiv-map-left-absorption-prod
d_is'45'equiv'45'map'45'left'45'absorption'45'prod_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'left'45'absorption'45'prod_124 ~v0 ~v1
  = du_is'45'equiv'45'map'45'left'45'absorption'45'prod_124
du_is'45'equiv'45'map'45'left'45'absorption'45'prod_124 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'left'45'absorption'45'prod_124
  = coe du_is'45'equiv'45'map'45'left'45'absorption'45'Σ_78
-- foundation.type-arithmetic-empty-type._.left-absorption-prod
d_left'45'absorption'45'prod_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_left'45'absorption'45'prod_128 ~v0 ~v1
  = du_left'45'absorption'45'prod_128
du_left'45'absorption'45'prod_128 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_left'45'absorption'45'prod_128
  = coe du_left'45'absorption'45'Σ_80
-- foundation.type-arithmetic-empty-type.is-empty-left-factor-is-empty-prod
d_is'45'empty'45'left'45'factor'45'is'45'empty'45'prod_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'left'45'factor'45'is'45'empty'45'prod_140 = erased
-- foundation.type-arithmetic-empty-type._.map-left-unit-law-coprod-is-empty
d_map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_162 ~v0 ~v1
                                                          ~v2 ~v3 ~v4 v5
  = du_map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_162 v5
du_map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_162 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
du_map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_162 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
             erased
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.type-arithmetic-empty-type._.map-inv-left-unit-law-coprod-is-empty
d_map'45'inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_168 ~v0
                                                                 ~v1 ~v2 ~v3 ~v4
  = du_map'45'inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_168
du_map'45'inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_168 ::
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_168
  = coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
-- foundation.type-arithmetic-empty-type._.issec-map-inv-left-unit-law-coprod-is-empty
d_issec'45'map'45'inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_170
  = erased
-- foundation.type-arithmetic-empty-type._.isretr-map-inv-left-unit-law-coprod-is-empty
d_isretr'45'map'45'inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_172
  = erased
-- foundation.type-arithmetic-empty-type._.is-equiv-map-left-unit-law-coprod-is-empty
d_is'45'equiv'45'map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_178 ~v0
                                                                         ~v1 ~v2 ~v3 ~v4
  = du_is'45'equiv'45'map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_178
du_is'45'equiv'45'map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_178 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_178
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe
         du_map'45'inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_168)
      erased erased
-- foundation.type-arithmetic-empty-type._.left-unit-law-coprod-is-empty
d_left'45'unit'45'law'45'coprod'45'is'45'empty_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_left'45'unit'45'law'45'coprod'45'is'45'empty_180 ~v0 ~v1 ~v2 ~v3
                                                   ~v4
  = du_left'45'unit'45'law'45'coprod'45'is'45'empty_180
du_left'45'unit'45'law'45'coprod'45'is'45'empty_180 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_left'45'unit'45'law'45'coprod'45'is'45'empty_180
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_162)
      (coe
         du_is'45'equiv'45'map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_178)
-- foundation.type-arithmetic-empty-type._.inv-left-unit-law-coprod-is-empty
d_inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_182 ~v0 ~v1
                                                          ~v2 ~v3 ~v4
  = du_inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_182
du_inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_182 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_182
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         du_map'45'inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_168)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
         (coe du_map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_162)
         erased erased)
-- foundation.type-arithmetic-empty-type._.is-empty-left-summand-is-equiv
d_is'45'empty'45'left'45'summand'45'is'45'equiv_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'left'45'summand'45'is'45'equiv_196 = erased
-- foundation.type-arithmetic-empty-type._.map-left-unit-law-coprod
d_map'45'left'45'unit'45'law'45'coprod_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_map'45'left'45'unit'45'law'45'coprod_210 ~v0 ~v1
  = du_map'45'left'45'unit'45'law'45'coprod_210
du_map'45'left'45'unit'45'law'45'coprod_210 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
du_map'45'left'45'unit'45'law'45'coprod_210
  = coe du_map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_162
-- foundation.type-arithmetic-empty-type._.map-inv-left-unit-law-coprod
d_map'45'inv'45'left'45'unit'45'law'45'coprod_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'inv'45'left'45'unit'45'law'45'coprod_212 ~v0 ~v1
  = du_map'45'inv'45'left'45'unit'45'law'45'coprod_212
du_map'45'inv'45'left'45'unit'45'law'45'coprod_212 ::
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'inv'45'left'45'unit'45'law'45'coprod_212
  = coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
-- foundation.type-arithmetic-empty-type._.issec-map-inv-left-unit-law-coprod
d_issec'45'map'45'inv'45'left'45'unit'45'law'45'coprod_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'left'45'unit'45'law'45'coprod_214 = erased
-- foundation.type-arithmetic-empty-type._.isretr-map-inv-left-unit-law-coprod
d_isretr'45'map'45'inv'45'left'45'unit'45'law'45'coprod_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'left'45'unit'45'law'45'coprod_216
  = erased
-- foundation.type-arithmetic-empty-type._.is-equiv-map-left-unit-law-coprod
d_is'45'equiv'45'map'45'left'45'unit'45'law'45'coprod_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'left'45'unit'45'law'45'coprod_218 ~v0 ~v1
  = du_is'45'equiv'45'map'45'left'45'unit'45'law'45'coprod_218
du_is'45'equiv'45'map'45'left'45'unit'45'law'45'coprod_218 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'left'45'unit'45'law'45'coprod_218
  = coe
      du_is'45'equiv'45'map'45'left'45'unit'45'law'45'coprod'45'is'45'empty_178
-- foundation.type-arithmetic-empty-type._.left-unit-law-coprod
d_left'45'unit'45'law'45'coprod_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_left'45'unit'45'law'45'coprod_220 ~v0 ~v1
  = du_left'45'unit'45'law'45'coprod_220
du_left'45'unit'45'law'45'coprod_220 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_left'45'unit'45'law'45'coprod_220
  = coe du_left'45'unit'45'law'45'coprod'45'is'45'empty_180
-- foundation.type-arithmetic-empty-type._.inv-left-unit-law-coprod
d_inv'45'left'45'unit'45'law'45'coprod_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'left'45'unit'45'law'45'coprod_222 ~v0 ~v1
  = du_inv'45'left'45'unit'45'law'45'coprod_222
du_inv'45'left'45'unit'45'law'45'coprod_222 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'left'45'unit'45'law'45'coprod_222
  = coe du_inv'45'left'45'unit'45'law'45'coprod'45'is'45'empty_182
-- foundation.type-arithmetic-empty-type._.map-right-unit-law-coprod-is-empty
d_map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_238 ~v0 ~v1
                                                           ~v2 ~v3 ~v4 v5
  = du_map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_238 v5
du_map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_238 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
du_map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_238 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1 -> coe v1
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.type-arithmetic-empty-type._.map-inv-right-unit-law-coprod-is-empty
d_map'45'inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_244 ~v0
                                                                  ~v1 ~v2 ~v3 ~v4
  = du_map'45'inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_244
du_map'45'inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_244 ::
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_244
  = coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
-- foundation.type-arithmetic-empty-type._.issec-map-inv-right-unit-law-coprod-is-empty
d_issec'45'map'45'inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_246
  = erased
-- foundation.type-arithmetic-empty-type._.isretr-map-inv-right-unit-law-coprod-is-empty
d_isretr'45'map'45'inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_250
  = erased
-- foundation.type-arithmetic-empty-type._.is-equiv-map-right-unit-law-coprod-is-empty
d_is'45'equiv'45'map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_256 ~v0
                                                                          ~v1 ~v2 ~v3 ~v4
  = du_is'45'equiv'45'map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_256
du_is'45'equiv'45'map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_256 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_256
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe
         du_map'45'inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_244)
      erased erased
-- foundation.type-arithmetic-empty-type._.is-equiv-inl-is-empty
d_is'45'equiv'45'inl'45'is'45'empty_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'inl'45'is'45'empty_258 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_is'45'equiv'45'inl'45'is'45'empty_258
du_is'45'equiv'45'inl'45'is'45'empty_258 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'inl'45'is'45'empty_258
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_238)
      erased erased
-- foundation.type-arithmetic-empty-type._.right-unit-law-coprod-is-empty
d_right'45'unit'45'law'45'coprod'45'is'45'empty_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_right'45'unit'45'law'45'coprod'45'is'45'empty_260 ~v0 ~v1 ~v2 ~v3
                                                    ~v4
  = du_right'45'unit'45'law'45'coprod'45'is'45'empty_260
du_right'45'unit'45'law'45'coprod'45'is'45'empty_260 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_right'45'unit'45'law'45'coprod'45'is'45'empty_260
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_238)
      (coe
         du_is'45'equiv'45'map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_256)
-- foundation.type-arithmetic-empty-type._.inv-right-unit-law-coprod-is-empty
d_inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_262 ~v0 ~v1
                                                           ~v2 ~v3 ~v4
  = du_inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_262
du_inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_262 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_262
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
         (coe du_map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_238)
         erased erased)
-- foundation.type-arithmetic-empty-type._.is-empty-right-summand-is-equiv
d_is'45'empty'45'right'45'summand'45'is'45'equiv_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'right'45'summand'45'is'45'equiv_276 = erased
-- foundation.type-arithmetic-empty-type._.map-right-unit-law-coprod
d_map'45'right'45'unit'45'law'45'coprod_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_map'45'right'45'unit'45'law'45'coprod_290 ~v0 ~v1
  = du_map'45'right'45'unit'45'law'45'coprod_290
du_map'45'right'45'unit'45'law'45'coprod_290 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
du_map'45'right'45'unit'45'law'45'coprod_290
  = coe du_map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_238
-- foundation.type-arithmetic-empty-type._.map-inv-right-unit-law-coprod
d_map'45'inv'45'right'45'unit'45'law'45'coprod_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'inv'45'right'45'unit'45'law'45'coprod_292 ~v0 ~v1
  = du_map'45'inv'45'right'45'unit'45'law'45'coprod_292
du_map'45'inv'45'right'45'unit'45'law'45'coprod_292 ::
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'inv'45'right'45'unit'45'law'45'coprod_292
  = coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
-- foundation.type-arithmetic-empty-type._.issec-map-inv-right-unit-law-coprod
d_issec'45'map'45'inv'45'right'45'unit'45'law'45'coprod_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'right'45'unit'45'law'45'coprod_294
  = erased
-- foundation.type-arithmetic-empty-type._.isretr-map-inv-right-unit-law-coprod
d_isretr'45'map'45'inv'45'right'45'unit'45'law'45'coprod_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'right'45'unit'45'law'45'coprod_296
  = erased
-- foundation.type-arithmetic-empty-type._.is-equiv-map-right-unit-law-coprod
d_is'45'equiv'45'map'45'right'45'unit'45'law'45'coprod_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'right'45'unit'45'law'45'coprod_298 ~v0 ~v1
  = du_is'45'equiv'45'map'45'right'45'unit'45'law'45'coprod_298
du_is'45'equiv'45'map'45'right'45'unit'45'law'45'coprod_298 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'right'45'unit'45'law'45'coprod_298
  = coe
      du_is'45'equiv'45'map'45'right'45'unit'45'law'45'coprod'45'is'45'empty_256
-- foundation.type-arithmetic-empty-type._.right-unit-law-coprod
d_right'45'unit'45'law'45'coprod_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_right'45'unit'45'law'45'coprod_300 ~v0 ~v1
  = du_right'45'unit'45'law'45'coprod_300
du_right'45'unit'45'law'45'coprod_300 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_right'45'unit'45'law'45'coprod_300
  = coe du_right'45'unit'45'law'45'coprod'45'is'45'empty_260
-- foundation.type-arithmetic-empty-type._.inv-right-unit-law-coprod
d_inv'45'right'45'unit'45'law'45'coprod_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'right'45'unit'45'law'45'coprod_302 ~v0 ~v1
  = du_inv'45'right'45'unit'45'law'45'coprod_302
du_inv'45'right'45'unit'45'law'45'coprod_302 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'right'45'unit'45'law'45'coprod_302
  = coe du_inv'45'right'45'unit'45'law'45'coprod'45'is'45'empty_262
