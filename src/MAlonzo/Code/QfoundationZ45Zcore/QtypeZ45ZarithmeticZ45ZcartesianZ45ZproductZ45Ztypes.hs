{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZcartesianZ45ZproductZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes

-- foundation-core.type-arithmetic-cartesian-product-types._.map-commutative-prod
d_map'45'commutative'45'prod_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'commutative'45'prod_16 ~v0 ~v1 ~v2 ~v3 v4
  = du_map'45'commutative'45'prod_16 v4
du_map'45'commutative'45'prod_16 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'commutative'45'prod_16 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- foundation-core.type-arithmetic-cartesian-product-types._.map-inv-commutative-prod
d_map'45'inv'45'commutative'45'prod_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'commutative'45'prod_26 ~v0 ~v1 ~v2 ~v3 v4
  = du_map'45'inv'45'commutative'45'prod_26 v4
du_map'45'inv'45'commutative'45'prod_26 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'commutative'45'prod_26 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- foundation-core.type-arithmetic-cartesian-product-types._.issec-map-inv-commutative-prod
d_issec'45'map'45'inv'45'commutative'45'prod_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'commutative'45'prod_36 = erased
-- foundation-core.type-arithmetic-cartesian-product-types._.isretr-map-inv-commutative-prod
d_isretr'45'map'45'inv'45'commutative'45'prod_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'commutative'45'prod_42 = erased
-- foundation-core.type-arithmetic-cartesian-product-types._.is-equiv-map-commutative-prod
d_is'45'equiv'45'map'45'commutative'45'prod_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'commutative'45'prod_48 ~v0 ~v1 ~v2 ~v3
  = du_is'45'equiv'45'map'45'commutative'45'prod_48
du_is'45'equiv'45'map'45'commutative'45'prod_48 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'commutative'45'prod_48
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'commutative'45'prod_26) erased erased
-- foundation-core.type-arithmetic-cartesian-product-types._.commutative-prod
d_commutative'45'prod_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_commutative'45'prod_50 ~v0 ~v1 ~v2 ~v3
  = du_commutative'45'prod_50
du_commutative'45'prod_50 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_commutative'45'prod_50
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'commutative'45'prod_16)
      (coe du_is'45'equiv'45'map'45'commutative'45'prod_48)
-- foundation-core.type-arithmetic-cartesian-product-types._.map-assoc-prod
d_map'45'assoc'45'prod_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'assoc'45'prod_68 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_map'45'assoc'45'prod_68
du_map'45'assoc'45'prod_68 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'assoc'45'prod_68
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_map'45'assoc'45'Σ_118
-- foundation-core.type-arithmetic-cartesian-product-types._.map-inv-assoc-prod
d_map'45'inv'45'assoc'45'prod_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'assoc'45'prod_74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_map'45'inv'45'assoc'45'prod_74
du_map'45'inv'45'assoc'45'prod_74 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'assoc'45'prod_74
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_map'45'inv'45'assoc'45'Σ_130
-- foundation-core.type-arithmetic-cartesian-product-types._.issec-map-inv-assoc-prod
d_issec'45'map'45'inv'45'assoc'45'prod_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'assoc'45'prod_80 = erased
-- foundation-core.type-arithmetic-cartesian-product-types._.isretr-map-inv-assoc-prod
d_isretr'45'map'45'inv'45'assoc'45'prod_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'assoc'45'prod_86 = erased
-- foundation-core.type-arithmetic-cartesian-product-types._.is-equiv-map-assoc-prod
d_is'45'equiv'45'map'45'assoc'45'prod_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'assoc'45'prod_92 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'assoc'45'prod_92
du_is'45'equiv'45'map'45'assoc'45'prod_92 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'assoc'45'prod_92
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_is'45'equiv'45'map'45'assoc'45'Σ_154
-- foundation-core.type-arithmetic-cartesian-product-types._.assoc-prod
d_assoc'45'prod_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_assoc'45'prod_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_assoc'45'prod_98
du_assoc'45'prod_98 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_assoc'45'prod_98
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_assoc'45'Σ_160
-- foundation-core.type-arithmetic-cartesian-product-types._.right-unit-law-prod-is-contr
d_right'45'unit'45'law'45'prod'45'is'45'contr_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_right'45'unit'45'law'45'prod'45'is'45'contr_116 ~v0 ~v1 ~v2 ~v3
                                                  v4
  = du_right'45'unit'45'law'45'prod'45'is'45'contr_116 v4
du_right'45'unit'45'law'45'prod'45'is'45'contr_116 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_right'45'unit'45'law'45'prod'45'is'45'contr_116 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_right'45'unit'45'law'45'Σ'45'is'45'contr_88
      (\ v1 -> v0)
-- foundation-core.type-arithmetic-cartesian-product-types._.left-unit-law-prod-is-contr
d_left'45'unit'45'law'45'prod'45'is'45'contr_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_left'45'unit'45'law'45'prod'45'is'45'contr_136 ~v0 ~v1 ~v2 ~v3 v4
  = du_left'45'unit'45'law'45'prod'45'is'45'contr_136 v4
du_left'45'unit'45'law'45'prod'45'is'45'contr_136 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_left'45'unit'45'law'45'prod'45'is'45'contr_136 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_left'45'unit'45'law'45'Σ'45'is'45'contr_52
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe v0))
