{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZcoproductZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes

-- foundation.type-arithmetic-coproduct-types._.map-commutative-coprod
d_map'45'commutative'45'coprod_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'commutative'45'coprod_16 ~v0 ~v1 ~v2 ~v3 v4
  = du_map'45'commutative'45'coprod_16 v4
du_map'45'commutative'45'coprod_16 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'commutative'45'coprod_16 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v1)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.type-arithmetic-coproduct-types._.map-inv-commutative-coprod
d_map'45'inv'45'commutative'45'coprod_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'inv'45'commutative'45'coprod_22 ~v0 ~v1 ~v2 ~v3 v4
  = du_map'45'inv'45'commutative'45'coprod_22 v4
du_map'45'inv'45'commutative'45'coprod_22 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'inv'45'commutative'45'coprod_22 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v1)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.type-arithmetic-coproduct-types._.issec-map-inv-commutative-coprod
d_issec'45'map'45'inv'45'commutative'45'coprod_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'commutative'45'coprod_28 = erased
-- foundation.type-arithmetic-coproduct-types._.isretr-map-inv-commutative-coprod
d_isretr'45'map'45'inv'45'commutative'45'coprod_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'commutative'45'coprod_34 = erased
-- foundation.type-arithmetic-coproduct-types._.is-equiv-map-commutative-coprod
d_is'45'equiv'45'map'45'commutative'45'coprod_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'commutative'45'coprod_40 ~v0 ~v1 ~v2 ~v3
  = du_is'45'equiv'45'map'45'commutative'45'coprod_40
du_is'45'equiv'45'map'45'commutative'45'coprod_40 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'commutative'45'coprod_40
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'commutative'45'coprod_22) erased erased
-- foundation.type-arithmetic-coproduct-types._.map-assoc-coprod
d_map'45'assoc'45'coprod_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'assoc'45'coprod_58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_map'45'assoc'45'coprod_58 v6
du_map'45'assoc'45'coprod_58 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'assoc'45'coprod_58 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2 -> coe v1
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe
                       MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.type-arithmetic-coproduct-types._.map-inv-assoc-coprod
d_map'45'inv'45'assoc'45'coprod_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'inv'45'assoc'45'coprod_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_map'45'inv'45'assoc'45'coprod_66 v6
du_map'45'inv'45'assoc'45'coprod_66 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'inv'45'assoc'45'coprod_66 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v0)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                    (coe
                       MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v2))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.type-arithmetic-coproduct-types._.issec-map-inv-assoc-coprod
d_issec'45'map'45'inv'45'assoc'45'coprod_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'assoc'45'coprod_74 = erased
-- foundation.type-arithmetic-coproduct-types._.isretr-map-inv-assoc-coprod
d_isretr'45'map'45'inv'45'assoc'45'coprod_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'assoc'45'coprod_82 = erased
-- foundation.type-arithmetic-coproduct-types._.is-equiv-map-assoc-coprod
d_is'45'equiv'45'map'45'assoc'45'coprod_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'assoc'45'coprod_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'assoc'45'coprod_90
du_is'45'equiv'45'map'45'assoc'45'coprod_90 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'assoc'45'coprod_90
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'assoc'45'coprod_66) erased erased
-- foundation.type-arithmetic-coproduct-types._.is-equiv-map-inv-assoc-coprod
d_is'45'equiv'45'map'45'inv'45'assoc'45'coprod_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'inv'45'assoc'45'coprod_92 ~v0 ~v1 ~v2 ~v3
                                                  ~v4 ~v5
  = du_is'45'equiv'45'map'45'inv'45'assoc'45'coprod_92
du_is'45'equiv'45'map'45'inv'45'assoc'45'coprod_92 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'inv'45'assoc'45'coprod_92
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'assoc'45'coprod_58) erased erased
-- foundation.type-arithmetic-coproduct-types._.assoc-coprod
d_assoc'45'coprod_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_assoc'45'coprod_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_assoc'45'coprod_94
du_assoc'45'coprod_94 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_assoc'45'coprod_94
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'assoc'45'coprod_58)
      (coe du_is'45'equiv'45'map'45'assoc'45'coprod_90)
-- foundation.type-arithmetic-coproduct-types._.inv-assoc-coprod
d_inv'45'assoc'45'coprod_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'assoc'45'coprod_96 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_inv'45'assoc'45'coprod_96
du_inv'45'assoc'45'coprod_96 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'assoc'45'coprod_96
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'inv'45'assoc'45'coprod_66)
      (coe du_is'45'equiv'45'map'45'inv'45'assoc'45'coprod_92)
-- foundation.type-arithmetic-coproduct-types._.map-right-distributive-Σ-coprod
d_map'45'right'45'distributive'45'Σ'45'coprod_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'right'45'distributive'45'Σ'45'coprod_118 ~v0 ~v1 ~v2 ~v3
                                                  ~v4 ~v5 v6
  = du_map'45'right'45'distributive'45'Σ'45'coprod_118 v6
du_map'45'right'45'distributive'45'Σ'45'coprod_118 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'right'45'distributive'45'Σ'45'coprod_118 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                       (coe v3) (coe v2))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                       (coe v3) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.type-arithmetic-coproduct-types._.map-inv-right-distributive-Σ-coprod
d_map'45'inv'45'right'45'distributive'45'Σ'45'coprod_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'right'45'distributive'45'Σ'45'coprod_132 ~v0 ~v1
                                                         ~v2 ~v3 ~v4 ~v5 v6
  = du_map'45'inv'45'right'45'distributive'45'Σ'45'coprod_132 v6
du_map'45'inv'45'right'45'distributive'45'Σ'45'coprod_132 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'right'45'distributive'45'Σ'45'coprod_132 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
                  -> coe
                       MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
                  -> coe
                       MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      (case coe v0 of
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
                  -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
                  -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- foundation.type-arithmetic-coproduct-types._.issec-map-inv-right-distributive-Σ-coprod
d_issec'45'map'45'inv'45'right'45'distributive'45'Σ'45'coprod_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'right'45'distributive'45'Σ'45'coprod_150
  = erased
-- foundation.type-arithmetic-coproduct-types._.isretr-map-inv-right-distributive-Σ-coprod
d_isretr'45'map'45'inv'45'right'45'distributive'45'Σ'45'coprod_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'right'45'distributive'45'Σ'45'coprod_160
  = erased
-- foundation.type-arithmetic-coproduct-types._.is-equiv-map-right-distributive-Σ-coprod
d_is'45'equiv'45'map'45'right'45'distributive'45'Σ'45'coprod_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'right'45'distributive'45'Σ'45'coprod_170 ~v0
                                                                 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'right'45'distributive'45'Σ'45'coprod_170
du_is'45'equiv'45'map'45'right'45'distributive'45'Σ'45'coprod_170 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'right'45'distributive'45'Σ'45'coprod_170
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'right'45'distributive'45'Σ'45'coprod_132)
      erased erased
-- foundation.type-arithmetic-coproduct-types._.right-distributive-Σ-coprod
d_right'45'distributive'45'Σ'45'coprod_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_right'45'distributive'45'Σ'45'coprod_176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_right'45'distributive'45'Σ'45'coprod_176
du_right'45'distributive'45'Σ'45'coprod_176 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_right'45'distributive'45'Σ'45'coprod_176
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'right'45'distributive'45'Σ'45'coprod_118)
      (coe
         du_is'45'equiv'45'map'45'right'45'distributive'45'Σ'45'coprod_170)
-- foundation.type-arithmetic-coproduct-types._.map-left-distributive-Σ-coprod
d_map'45'left'45'distributive'45'Σ'45'coprod_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'left'45'distributive'45'Σ'45'coprod_196 ~v0 ~v1 ~v2 ~v3
                                                 ~v4 ~v5 v6
  = du_map'45'left'45'distributive'45'Σ'45'coprod_196 v6
du_map'45'left'45'distributive'45'Σ'45'coprod_196 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'left'45'distributive'45'Σ'45'coprod_196 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                       (coe v1) (coe v3))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                       (coe v1) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.type-arithmetic-coproduct-types._.map-inv-left-distributive-Σ-coprod
d_map'45'inv'45'left'45'distributive'45'Σ'45'coprod_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'left'45'distributive'45'Σ'45'coprod_208 ~v0 ~v1 ~v2
                                                        ~v3 ~v4 ~v5 v6
  = du_map'45'inv'45'left'45'distributive'45'Σ'45'coprod_208 v6
du_map'45'inv'45'left'45'distributive'45'Σ'45'coprod_208 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'left'45'distributive'45'Σ'45'coprod_208 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
                  -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
                  -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      (case coe v0 of
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
                  -> coe
                       MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v3)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
                  -> coe
                       MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v3)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- foundation.type-arithmetic-coproduct-types._.issec-map-inv-left-distributive-Σ-coprod
d_issec'45'map'45'inv'45'left'45'distributive'45'Σ'45'coprod_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'left'45'distributive'45'Σ'45'coprod_226
  = erased
-- foundation.type-arithmetic-coproduct-types._.isretr-map-inv-left-distributive-Σ-coprod
d_isretr'45'map'45'inv'45'left'45'distributive'45'Σ'45'coprod_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'left'45'distributive'45'Σ'45'coprod_236
  = erased
-- foundation.type-arithmetic-coproduct-types._.is-equiv-map-left-distributive-Σ-coprod
d_is'45'equiv'45'map'45'left'45'distributive'45'Σ'45'coprod_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'left'45'distributive'45'Σ'45'coprod_246 ~v0
                                                                ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'left'45'distributive'45'Σ'45'coprod_246
du_is'45'equiv'45'map'45'left'45'distributive'45'Σ'45'coprod_246 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'left'45'distributive'45'Σ'45'coprod_246
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'left'45'distributive'45'Σ'45'coprod_208)
      erased erased
-- foundation.type-arithmetic-coproduct-types._.left-distributive-Σ-coprod
d_left'45'distributive'45'Σ'45'coprod_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_left'45'distributive'45'Σ'45'coprod_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_left'45'distributive'45'Σ'45'coprod_250
du_left'45'distributive'45'Σ'45'coprod_250 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_left'45'distributive'45'Σ'45'coprod_250
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'left'45'distributive'45'Σ'45'coprod_196)
      (coe
         du_is'45'equiv'45'map'45'left'45'distributive'45'Σ'45'coprod_246)
-- foundation.type-arithmetic-coproduct-types._.map-right-distributive-prod-coprod
d_map'45'right'45'distributive'45'prod'45'coprod_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'right'45'distributive'45'prod'45'coprod_268 ~v0 ~v1 ~v2
                                                     ~v3 ~v4 ~v5
  = du_map'45'right'45'distributive'45'prod'45'coprod_268
du_map'45'right'45'distributive'45'prod'45'coprod_268 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'right'45'distributive'45'prod'45'coprod_268
  = coe du_map'45'right'45'distributive'45'Σ'45'coprod_118
-- foundation.type-arithmetic-coproduct-types._.map-inv-right-distributive-prod-coprod
d_map'45'inv'45'right'45'distributive'45'prod'45'coprod_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'right'45'distributive'45'prod'45'coprod_272 ~v0 ~v1
                                                            ~v2 ~v3 ~v4 ~v5
  = du_map'45'inv'45'right'45'distributive'45'prod'45'coprod_272
du_map'45'inv'45'right'45'distributive'45'prod'45'coprod_272 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'right'45'distributive'45'prod'45'coprod_272
  = coe du_map'45'inv'45'right'45'distributive'45'Σ'45'coprod_132
-- foundation.type-arithmetic-coproduct-types._.issec-map-inv-right-distributive-prod-coprod
d_issec'45'map'45'inv'45'right'45'distributive'45'prod'45'coprod_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'right'45'distributive'45'prod'45'coprod_276
  = erased
-- foundation.type-arithmetic-coproduct-types._.isretr-map-inv-right-distributive-prod-coprod
d_isretr'45'map'45'inv'45'right'45'distributive'45'prod'45'coprod_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'right'45'distributive'45'prod'45'coprod_280
  = erased
-- foundation.type-arithmetic-coproduct-types._.is-equiv-map-right-distributive-prod-coprod
d_is'45'equiv'45'map'45'right'45'distributive'45'prod'45'coprod_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'right'45'distributive'45'prod'45'coprod_284 ~v0
                                                                    ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'right'45'distributive'45'prod'45'coprod_284
du_is'45'equiv'45'map'45'right'45'distributive'45'prod'45'coprod_284 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'right'45'distributive'45'prod'45'coprod_284
  = coe
      du_is'45'equiv'45'map'45'right'45'distributive'45'Σ'45'coprod_170
-- foundation.type-arithmetic-coproduct-types._.right-distributive-prod-coprod
d_right'45'distributive'45'prod'45'coprod_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_right'45'distributive'45'prod'45'coprod_288 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5
  = du_right'45'distributive'45'prod'45'coprod_288
du_right'45'distributive'45'prod'45'coprod_288 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_right'45'distributive'45'prod'45'coprod_288
  = coe du_right'45'distributive'45'Σ'45'coprod_176
-- foundation.type-arithmetic-coproduct-types._.map-left-distributive-prod-coprod
d_map'45'left'45'distributive'45'prod'45'coprod_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'left'45'distributive'45'prod'45'coprod_308 ~v0 ~v1 ~v2 ~v3
                                                    ~v4 ~v5
  = du_map'45'left'45'distributive'45'prod'45'coprod_308
du_map'45'left'45'distributive'45'prod'45'coprod_308 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'left'45'distributive'45'prod'45'coprod_308
  = coe du_map'45'left'45'distributive'45'Σ'45'coprod_196
-- foundation.type-arithmetic-coproduct-types._.map-inv-left-distributive-prod-coprod
d_map'45'inv'45'left'45'distributive'45'prod'45'coprod_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'left'45'distributive'45'prod'45'coprod_314 ~v0 ~v1
                                                           ~v2 ~v3 ~v4 ~v5
  = du_map'45'inv'45'left'45'distributive'45'prod'45'coprod_314
du_map'45'inv'45'left'45'distributive'45'prod'45'coprod_314 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'left'45'distributive'45'prod'45'coprod_314
  = coe du_map'45'inv'45'left'45'distributive'45'Σ'45'coprod_208
-- foundation.type-arithmetic-coproduct-types._.issec-map-inv-left-distributive-prod-coprod
d_issec'45'map'45'inv'45'left'45'distributive'45'prod'45'coprod_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'left'45'distributive'45'prod'45'coprod_320
  = erased
-- foundation.type-arithmetic-coproduct-types._.isretr-map-inv-left-distributive-prod-coprod
d_isretr'45'map'45'inv'45'left'45'distributive'45'prod'45'coprod_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'left'45'distributive'45'prod'45'coprod_326
  = erased
-- foundation.type-arithmetic-coproduct-types._.is-equiv-map-left-distributive-prod-coprod
d_is'45'equiv'45'map'45'left'45'distributive'45'prod'45'coprod_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'left'45'distributive'45'prod'45'coprod_332 ~v0
                                                                   ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'left'45'distributive'45'prod'45'coprod_332
du_is'45'equiv'45'map'45'left'45'distributive'45'prod'45'coprod_332 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'left'45'distributive'45'prod'45'coprod_332
  = coe
      du_is'45'equiv'45'map'45'left'45'distributive'45'Σ'45'coprod_246
-- foundation.type-arithmetic-coproduct-types._.left-distributive-prod-coprod
d_left'45'distributive'45'prod'45'coprod_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_left'45'distributive'45'prod'45'coprod_338 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5
  = du_left'45'distributive'45'prod'45'coprod_338
du_left'45'distributive'45'prod'45'coprod_338 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_left'45'distributive'45'prod'45'coprod_338
  = coe du_left'45'distributive'45'Σ'45'coprod_250
