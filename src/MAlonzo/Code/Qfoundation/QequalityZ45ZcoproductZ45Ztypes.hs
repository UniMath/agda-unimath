{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QequalityZ45ZcoproductZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes

-- foundation.equality-coproduct-types._.Eq-coprod
d_Eq'45'coprod_16 a0 a1 a2 a3 a4 a5 = ()
data T_Eq'45'coprod_16
  = C_Eq'45'eq'45'coprod'45'inl_22 | C_Eq'45'eq'45'coprod'45'inr_28
-- foundation.equality-coproduct-types._.refl-Eq-coprod
d_refl'45'Eq'45'coprod_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  T_Eq'45'coprod_16
d_refl'45'Eq'45'coprod_44 ~v0 ~v1 ~v2 ~v3 v4
  = du_refl'45'Eq'45'coprod_44 v4
du_refl'45'Eq'45'coprod_44 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  T_Eq'45'coprod_16
du_refl'45'Eq'45'coprod_44 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe C_Eq'45'eq'45'coprod'45'inl_22
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe C_Eq'45'eq'45'coprod'45'inr_28
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.equality-coproduct-types._.Eq-eq-coprod
d_Eq'45'eq'45'coprod_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  T_Eq'45'coprod_16
d_Eq'45'eq'45'coprod_54 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_Eq'45'eq'45'coprod_54 v4
du_Eq'45'eq'45'coprod_54 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  T_Eq'45'coprod_16
du_Eq'45'eq'45'coprod_54 v0
  = coe du_refl'45'Eq'45'coprod_44 (coe v0)
-- foundation.equality-coproduct-types._.eq-Eq-coprod
d_eq'45'Eq'45'coprod_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  T_Eq'45'coprod_16 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'Eq'45'coprod_62 = erased
-- foundation.equality-coproduct-types._.is-contr-total-Eq-coprod
d_is'45'contr'45'total'45'Eq'45'coprod_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'Eq'45'coprod_70 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'contr'45'total'45'Eq'45'coprod_70 v4
du_is'45'contr'45'total'45'Eq'45'coprod_70 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'Eq'45'coprod_70 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v0)
         (case coe v0 of
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
              -> coe C_Eq'45'eq'45'coprod'45'inl_22
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
              -> coe C_Eq'45'eq'45'coprod'45'inr_28
            _ -> MAlonzo.RTE.mazUnreachableError))
      erased
-- foundation.equality-coproduct-types._.is-equiv-Eq-eq-coprod
d_is'45'equiv'45'Eq'45'eq'45'coprod_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'Eq'45'eq'45'coprod_88 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'equiv'45'Eq'45'eq'45'coprod_88 v4
du_is'45'equiv'45'Eq'45'eq'45'coprod_88 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'Eq'45'eq'45'coprod_88 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation.equality-coproduct-types._.extensionality-coprod
d_extensionality'45'coprod_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_extensionality'45'coprod_96 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_extensionality'45'coprod_96 v4 v5
du_extensionality'45'coprod_96 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_extensionality'45'coprod_96 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (\ v2 -> coe du_Eq'45'eq'45'coprod_54 (coe v0))
      (coe du_is'45'equiv'45'Eq'45'eq'45'coprod_88 v0 v1)
-- foundation.equality-coproduct-types._._.map-compute-Eq-coprod-inl-inl
d_map'45'compute'45'Eq'45'coprod'45'inl'45'inl_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T_Eq'45'coprod_16 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_map'45'compute'45'Eq'45'coprod'45'inl'45'inl_126 = erased
-- foundation.equality-coproduct-types._._.issec-Eq-eq-coprod-inl
d_issec'45'Eq'45'eq'45'coprod'45'inl_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'Eq'45'eq'45'coprod'45'inl_130 = erased
-- foundation.equality-coproduct-types._._.isretr-Eq-eq-coprod-inl
d_isretr'45'Eq'45'eq'45'coprod'45'inl_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T_Eq'45'coprod_16 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'Eq'45'eq'45'coprod'45'inl_134 = erased
-- foundation.equality-coproduct-types._._.is-equiv-map-compute-Eq-coprod-inl-inl
d_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inl'45'inl_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inl'45'inl_138 ~v0
                                                                  ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inl'45'inl_138
du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inl'45'inl_138 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inl'45'inl_138
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (\ v0 -> coe C_Eq'45'eq'45'coprod'45'inl_22) erased erased
-- foundation.equality-coproduct-types._._.compute-Eq-coprod-inl-inl
d_compute'45'Eq'45'coprod'45'inl'45'inl_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_compute'45'Eq'45'coprod'45'inl'45'inl_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_compute'45'Eq'45'coprod'45'inl'45'inl_140
du_compute'45'Eq'45'coprod'45'inl'45'inl_140 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_compute'45'Eq'45'coprod'45'inl'45'inl_140
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inl'45'inl_138)
-- foundation.equality-coproduct-types._._.compute-eq-coprod-inl-inl
d_compute'45'eq'45'coprod'45'inl'45'inl_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_compute'45'eq'45'coprod'45'inl'45'inl_142 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_compute'45'eq'45'coprod'45'inl'45'inl_142 v4 v5
du_compute'45'eq'45'coprod'45'inl'45'inl_142 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_compute'45'eq'45'coprod'45'inl'45'inl_142 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe du_compute'45'Eq'45'coprod'45'inl'45'inl_140)
      (coe
         du_extensionality'45'coprod_96
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v0))
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v1)))
-- foundation.equality-coproduct-types._._.map-compute-eq-coprod-inl-inl
d_map'45'compute'45'eq'45'coprod'45'inl'45'inl_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_map'45'compute'45'eq'45'coprod'45'inl'45'inl_144 = erased
-- foundation.equality-coproduct-types._._.map-compute-Eq-coprod-inl-inr
d_map'45'compute'45'Eq'45'coprod'45'inl'45'inr_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T_Eq'45'coprod_16 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_map'45'compute'45'Eq'45'coprod'45'inl'45'inr_154 = erased
-- foundation.equality-coproduct-types._._.is-equiv-map-compute-Eq-coprod-inl-inr
d_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inl'45'inr_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inl'45'inr_156 ~v0
                                                                  ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inl'45'inr_156
du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inl'45'inr_156 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inl'45'inr_156
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'equiv'45'is'45'empty''_70
-- foundation.equality-coproduct-types._._.compute-Eq-coprod-inl-inr
d_compute'45'Eq'45'coprod'45'inl'45'inr_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_compute'45'Eq'45'coprod'45'inl'45'inr_158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_compute'45'Eq'45'coprod'45'inl'45'inr_158
du_compute'45'Eq'45'coprod'45'inl'45'inr_158 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_compute'45'Eq'45'coprod'45'inl'45'inr_158
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inl'45'inr_156)
-- foundation.equality-coproduct-types._._.compute-eq-coprod-inl-inr
d_compute'45'eq'45'coprod'45'inl'45'inr_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_compute'45'eq'45'coprod'45'inl'45'inr_160 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_compute'45'eq'45'coprod'45'inl'45'inr_160 v4 v5
du_compute'45'eq'45'coprod'45'inl'45'inr_160 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_compute'45'eq'45'coprod'45'inl'45'inr_160 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe du_compute'45'Eq'45'coprod'45'inl'45'inr_158)
      (coe
         du_extensionality'45'coprod_96
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v0))
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v1)))
-- foundation.equality-coproduct-types._._.is-empty-eq-coprod-inl-inr
d_is'45'empty'45'eq'45'coprod'45'inl'45'inr_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'eq'45'coprod'45'inl'45'inr_162 = erased
-- foundation.equality-coproduct-types._._.map-compute-Eq-coprod-inr-inl
d_map'45'compute'45'Eq'45'coprod'45'inr'45'inl_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T_Eq'45'coprod_16 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_map'45'compute'45'Eq'45'coprod'45'inr'45'inl_172 = erased
-- foundation.equality-coproduct-types._._.is-equiv-map-compute-Eq-coprod-inr-inl
d_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inr'45'inl_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inr'45'inl_174 ~v0
                                                                  ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inr'45'inl_174
du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inr'45'inl_174 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inr'45'inl_174
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'equiv'45'is'45'empty''_70
-- foundation.equality-coproduct-types._._.compute-Eq-coprod-inr-inl
d_compute'45'Eq'45'coprod'45'inr'45'inl_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_compute'45'Eq'45'coprod'45'inr'45'inl_176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_compute'45'Eq'45'coprod'45'inr'45'inl_176
du_compute'45'Eq'45'coprod'45'inr'45'inl_176 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_compute'45'Eq'45'coprod'45'inr'45'inl_176
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inr'45'inl_174)
-- foundation.equality-coproduct-types._._.compute-eq-coprod-inr-inl
d_compute'45'eq'45'coprod'45'inr'45'inl_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_compute'45'eq'45'coprod'45'inr'45'inl_178 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_compute'45'eq'45'coprod'45'inr'45'inl_178 v4 v5
du_compute'45'eq'45'coprod'45'inr'45'inl_178 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_compute'45'eq'45'coprod'45'inr'45'inl_178 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe du_compute'45'Eq'45'coprod'45'inr'45'inl_176)
      (coe
         du_extensionality'45'coprod_96
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v0))
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v1)))
-- foundation.equality-coproduct-types._._.is-empty-eq-coprod-inr-inl
d_is'45'empty'45'eq'45'coprod'45'inr'45'inl_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'eq'45'coprod'45'inr'45'inl_180 = erased
-- foundation.equality-coproduct-types._._.map-compute-Eq-coprod-inr-inr
d_map'45'compute'45'Eq'45'coprod'45'inr'45'inr_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T_Eq'45'coprod_16 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_map'45'compute'45'Eq'45'coprod'45'inr'45'inr_190 = erased
-- foundation.equality-coproduct-types._._.issec-Eq-eq-coprod-inr
d_issec'45'Eq'45'eq'45'coprod'45'inr_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'Eq'45'eq'45'coprod'45'inr_194 = erased
-- foundation.equality-coproduct-types._._.isretr-Eq-eq-coprod-inr
d_isretr'45'Eq'45'eq'45'coprod'45'inr_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T_Eq'45'coprod_16 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'Eq'45'eq'45'coprod'45'inr_198 = erased
-- foundation.equality-coproduct-types._._.is-equiv-map-compute-Eq-coprod-inr-inr
d_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inr'45'inr_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inr'45'inr_202 ~v0
                                                                  ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inr'45'inr_202
du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inr'45'inr_202 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inr'45'inr_202
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (\ v0 -> coe C_Eq'45'eq'45'coprod'45'inr_28) erased erased
-- foundation.equality-coproduct-types._._.compute-Eq-coprod-inr-inr
d_compute'45'Eq'45'coprod'45'inr'45'inr_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_compute'45'Eq'45'coprod'45'inr'45'inr_204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_compute'45'Eq'45'coprod'45'inr'45'inr_204
du_compute'45'Eq'45'coprod'45'inr'45'inr_204 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_compute'45'Eq'45'coprod'45'inr'45'inr_204
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'equiv'45'map'45'compute'45'Eq'45'coprod'45'inr'45'inr_202)
-- foundation.equality-coproduct-types._._.compute-eq-coprod-inr-inr
d_compute'45'eq'45'coprod'45'inr'45'inr_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_compute'45'eq'45'coprod'45'inr'45'inr_206 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_compute'45'eq'45'coprod'45'inr'45'inr_206 v4 v5
du_compute'45'eq'45'coprod'45'inr'45'inr_206 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_compute'45'eq'45'coprod'45'inr'45'inr_206 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe du_compute'45'Eq'45'coprod'45'inr'45'inr_204)
      (coe
         du_extensionality'45'coprod_96
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v0))
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v1)))
-- foundation.equality-coproduct-types._._.map-compute-eq-coprod-inr-inr
d_map'45'compute'45'eq'45'coprod'45'inr'45'inr_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_map'45'compute'45'eq'45'coprod'45'inr'45'inr_208 = erased
-- foundation.equality-coproduct-types._.is-emb-inl
d_is'45'emb'45'inl_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'inl_222 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'emb'45'inl_222 v4
du_is'45'emb'45'inl_222 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'inl_222 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation.equality-coproduct-types._.emb-inl
d_emb'45'inl_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_emb'45'inl_228 ~v0 ~v1 ~v2 ~v3 = du_emb'45'inl_228
du_emb'45'inl_228 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_emb'45'inl_228
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22)
      (coe du_is'45'emb'45'inl_222)
-- foundation.equality-coproduct-types._.is-emb-inr
d_is'45'emb'45'inr_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'inr_230 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'emb'45'inr_230 v4
du_is'45'emb'45'inr_230 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'inr_230 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation.equality-coproduct-types._.emb-inr
d_emb'45'inr_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_emb'45'inr_236 ~v0 ~v1 ~v2 ~v3 = du_emb'45'inr_236
du_emb'45'inr_236 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_emb'45'inr_236
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24)
      (coe du_is'45'emb'45'inr_230)
-- foundation.equality-coproduct-types._.is-emb-coprod
d_is'45'emb'45'coprod_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'coprod_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                          ~v10 v11 v12
  = du_is'45'emb'45'coprod_264 v8 v9 v11 v12
du_is'45'emb'45'coprod_264 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'coprod_264 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
        -> case coe v3 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'left'45'factor_412
                    erased (coe v0 v4 v5) (coe du_is'45'emb'45'inl_222 v4 v5)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'equiv'45'is'45'empty_54
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
        -> case coe v3 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'equiv'45'is'45'empty_54
                    erased
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'left'45'factor_412
                    erased (coe v1 v4 v5) (coe du_is'45'emb'45'inr_230 v4 v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.equality-coproduct-types._.is-trunc-coprod
d_is'45'trunc'45'coprod_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   AgdaAny) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_is'45'trunc'45'coprod_336 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8
  = du_is'45'trunc'45'coprod_336 v2 v5 v6 v7 v8
du_is'45'trunc'45'coprod_336 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   AgdaAny) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
du_is'45'trunc'45'coprod_336 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
        -> case coe v4 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v6
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'equiv_206
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8
                       (coe v0))
                    (coe
                       du_compute'45'eq'45'coprod'45'inl'45'inl_142 (coe v5) (coe v6))
                    (coe v1 v5 v6)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v6
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'trunc'45'is'45'empty_116
                    (coe ()) (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
        -> case coe v4 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v6
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'trunc'45'is'45'empty_116
                    (coe ()) (coe v0)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v6
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'equiv_206
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8
                       (coe v0))
                    (coe
                       du_compute'45'eq'45'coprod'45'inr'45'inr_206 (coe v5) (coe v6))
                    (coe v2 v5 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.equality-coproduct-types.is-set-coprod
d_is'45'set'45'coprod_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'coprod_378 ~v0 ~v1 ~v2 ~v3
  = du_is'45'set'45'coprod_378
du_is'45'set'45'coprod_378 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'coprod_378
  = coe
      du_is'45'trunc'45'coprod_336
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6)
-- foundation.equality-coproduct-types.coprod-Set
d_coprod'45'Set_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_coprod'45'Set_388 ~v0 ~v1 v2 v3 = du_coprod'45'Set_388 v2 v3
du_coprod'45'Set_388 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_coprod'45'Set_388 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                  -> coe du_is'45'set'45'coprod_378 v3 v5
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
