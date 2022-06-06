{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZunitZ45Ztype where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- foundation.type-arithmetic-unit-type._.map-left-unit-law-Σ
d_map'45'left'45'unit'45'law'45'Σ_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_map'45'left'45'unit'45'law'45'Σ_12 ~v0 ~v1 v2
  = du_map'45'left'45'unit'45'law'45'Σ_12 v2
du_map'45'left'45'unit'45'law'45'Σ_12 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_map'45'left'45'unit'45'law'45'Σ_12 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.type-arithmetic-unit-type._.map-inv-left-unit-law-Σ
d_map'45'inv'45'left'45'unit'45'law'45'Σ_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> ()) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'left'45'unit'45'law'45'Σ_16 ~v0 ~v1 v2
  = du_map'45'inv'45'left'45'unit'45'law'45'Σ_16 v2
du_map'45'inv'45'left'45'unit'45'law'45'Σ_16 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'left'45'unit'45'law'45'Σ_16 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe v0)
-- foundation.type-arithmetic-unit-type._.issec-map-inv-left-unit-law-Σ
d_issec'45'map'45'inv'45'left'45'unit'45'law'45'Σ_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> ()) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'left'45'unit'45'law'45'Σ_22 = erased
-- foundation.type-arithmetic-unit-type._.isretr-map-inv-left-unit-law-Σ
d_isretr'45'map'45'inv'45'left'45'unit'45'law'45'Σ_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'left'45'unit'45'law'45'Σ_26 = erased
-- foundation.type-arithmetic-unit-type._.is-equiv-map-left-unit-law-Σ
d_is'45'equiv'45'map'45'left'45'unit'45'law'45'Σ_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'left'45'unit'45'law'45'Σ_30 ~v0 ~v1
  = du_is'45'equiv'45'map'45'left'45'unit'45'law'45'Σ_30
du_is'45'equiv'45'map'45'left'45'unit'45'law'45'Σ_30 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'left'45'unit'45'law'45'Σ_30
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'left'45'unit'45'law'45'Σ_16) erased erased
-- foundation.type-arithmetic-unit-type._.left-unit-law-Σ
d_left'45'unit'45'law'45'Σ_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_left'45'unit'45'law'45'Σ_32 ~v0 ~v1
  = du_left'45'unit'45'law'45'Σ_32
du_left'45'unit'45'law'45'Σ_32 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_left'45'unit'45'law'45'Σ_32
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'left'45'unit'45'law'45'Σ_12)
      (coe du_is'45'equiv'45'map'45'left'45'unit'45'law'45'Σ_30)
-- foundation.type-arithmetic-unit-type._.is-equiv-map-inv-left-unit-law-Σ
d_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'Σ_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'Σ_34 ~v0 ~v1
  = du_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'Σ_34
du_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'Σ_34 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'Σ_34
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'left'45'unit'45'law'45'Σ_12) erased erased
-- foundation.type-arithmetic-unit-type._.inv-left-unit-law-Σ
d_inv'45'left'45'unit'45'law'45'Σ_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'left'45'unit'45'law'45'Σ_36 ~v0 ~v1
  = du_inv'45'left'45'unit'45'law'45'Σ_36
du_inv'45'left'45'unit'45'law'45'Σ_36 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'left'45'unit'45'law'45'Σ_36
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'inv'45'left'45'unit'45'law'45'Σ_16)
      (coe du_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'Σ_34)
-- foundation.type-arithmetic-unit-type._.map-left-unit-law-prod
d_map'45'left'45'unit'45'law'45'prod_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_map'45'left'45'unit'45'law'45'prod_46 ~v0 ~v1
  = du_map'45'left'45'unit'45'law'45'prod_46
du_map'45'left'45'unit'45'law'45'prod_46 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_map'45'left'45'unit'45'law'45'prod_46
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
-- foundation.type-arithmetic-unit-type._.map-inv-left-unit-law-prod
d_map'45'inv'45'left'45'unit'45'law'45'prod_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'left'45'unit'45'law'45'prod_48 ~v0 ~v1
  = du_map'45'inv'45'left'45'unit'45'law'45'prod_48
du_map'45'inv'45'left'45'unit'45'law'45'prod_48 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'left'45'unit'45'law'45'prod_48
  = coe du_map'45'inv'45'left'45'unit'45'law'45'Σ_16
-- foundation.type-arithmetic-unit-type._.issec-map-inv-left-unit-law-prod
d_issec'45'map'45'inv'45'left'45'unit'45'law'45'prod_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'left'45'unit'45'law'45'prod_52 = erased
-- foundation.type-arithmetic-unit-type._.isretr-map-inv-left-unit-law-prod
d_isretr'45'map'45'inv'45'left'45'unit'45'law'45'prod_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'left'45'unit'45'law'45'prod_56 = erased
-- foundation.type-arithmetic-unit-type._.is-equiv-map-left-unit-law-prod
d_is'45'equiv'45'map'45'left'45'unit'45'law'45'prod_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'left'45'unit'45'law'45'prod_60 ~v0 ~v1
  = du_is'45'equiv'45'map'45'left'45'unit'45'law'45'prod_60
du_is'45'equiv'45'map'45'left'45'unit'45'law'45'prod_60 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'left'45'unit'45'law'45'prod_60
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'left'45'unit'45'law'45'prod_48) erased erased
-- foundation.type-arithmetic-unit-type._.left-unit-law-prod
d_left'45'unit'45'law'45'prod_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_left'45'unit'45'law'45'prod_62 ~v0 ~v1
  = du_left'45'unit'45'law'45'prod_62
du_left'45'unit'45'law'45'prod_62 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_left'45'unit'45'law'45'prod_62
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'left'45'unit'45'law'45'prod_46)
      (coe du_is'45'equiv'45'map'45'left'45'unit'45'law'45'prod_60)
-- foundation.type-arithmetic-unit-type._.is-equiv-map-inv-left-unit-law-prod
d_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'prod_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'prod_64 ~v0
                                                              ~v1
  = du_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'prod_64
du_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'prod_64 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'prod_64
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'left'45'unit'45'law'45'prod_46) erased erased
-- foundation.type-arithmetic-unit-type._.inv-left-unit-law-prod
d_inv'45'left'45'unit'45'law'45'prod_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'left'45'unit'45'law'45'prod_66 ~v0 ~v1
  = du_inv'45'left'45'unit'45'law'45'prod_66
du_inv'45'left'45'unit'45'law'45'prod_66 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'left'45'unit'45'law'45'prod_66
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'inv'45'left'45'unit'45'law'45'prod_48)
      (coe
         du_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'prod_64)
-- foundation.type-arithmetic-unit-type._.map-right-unit-law-prod
d_map'45'right'45'unit'45'law'45'prod_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_map'45'right'45'unit'45'law'45'prod_68 ~v0 ~v1
  = du_map'45'right'45'unit'45'law'45'prod_68
du_map'45'right'45'unit'45'law'45'prod_68 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_map'45'right'45'unit'45'law'45'prod_68
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
-- foundation.type-arithmetic-unit-type._.map-inv-right-unit-law-prod
d_map'45'inv'45'right'45'unit'45'law'45'prod_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'right'45'unit'45'law'45'prod_70 ~v0 ~v1 v2
  = du_map'45'inv'45'right'45'unit'45'law'45'prod_70 v2
du_map'45'inv'45'right'45'unit'45'law'45'prod_70 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'right'45'unit'45'law'45'prod_70 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe v0) erased
-- foundation.type-arithmetic-unit-type._.issec-map-inv-right-unit-law-prod
d_issec'45'map'45'inv'45'right'45'unit'45'law'45'prod_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'right'45'unit'45'law'45'prod_76 = erased
-- foundation.type-arithmetic-unit-type._.isretr-map-inv-right-unit-law-prod
d_isretr'45'map'45'inv'45'right'45'unit'45'law'45'prod_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'right'45'unit'45'law'45'prod_80 = erased
-- foundation.type-arithmetic-unit-type._.is-equiv-map-right-unit-law-prod
d_is'45'equiv'45'map'45'right'45'unit'45'law'45'prod_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'right'45'unit'45'law'45'prod_84 ~v0 ~v1
  = du_is'45'equiv'45'map'45'right'45'unit'45'law'45'prod_84
du_is'45'equiv'45'map'45'right'45'unit'45'law'45'prod_84 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'right'45'unit'45'law'45'prod_84
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'right'45'unit'45'law'45'prod_70) erased
      erased
-- foundation.type-arithmetic-unit-type._.right-unit-law-prod
d_right'45'unit'45'law'45'prod_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_right'45'unit'45'law'45'prod_86 ~v0 ~v1
  = du_right'45'unit'45'law'45'prod_86
du_right'45'unit'45'law'45'prod_86 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_right'45'unit'45'law'45'prod_86
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'right'45'unit'45'law'45'prod_68)
      (coe du_is'45'equiv'45'map'45'right'45'unit'45'law'45'prod_84)
