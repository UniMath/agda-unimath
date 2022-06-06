{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes

-- foundation.raising-universe-levels.raise
d_raise_10 a0 a1 a2 = ()
newtype T_raise_10 = C_map'45'raise_18 AgdaAny
-- foundation.raising-universe-levels._.map-inv-raise
d_map'45'inv'45'raise_30 :: T_raise_10 -> AgdaAny
d_map'45'inv'45'raise_30 v0
  = case coe v0 of
      C_map'45'raise_18 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.raising-universe-levels._.issec-map-inv-raise
d_issec'45'map'45'inv'45'raise_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  T_raise_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'raise_34 = erased
-- foundation.raising-universe-levels._.isretr-map-inv-raise
d_isretr'45'map'45'inv'45'raise_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'raise_38 = erased
-- foundation.raising-universe-levels._.is-equiv-map-raise
d_is'45'equiv'45'map'45'raise_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'raise_42 ~v0 ~v1 ~v2
  = du_is'45'equiv'45'map'45'raise_42
du_is'45'equiv'45'map'45'raise_42 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'raise_42
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe d_map'45'inv'45'raise_30) erased erased
-- foundation.raising-universe-levels.equiv-raise
d_equiv'45'raise_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'raise_50 ~v0 ~v1 ~v2 = du_equiv'45'raise_50
du_equiv'45'raise_50 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'raise_50
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe C_map'45'raise_18) (coe du_is'45'equiv'45'map'45'raise_42)
-- foundation.raising-universe-levels.Raise
d_Raise_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Raise_68 ~v0 ~v1 ~v2 = du_Raise_68
du_Raise_68 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Raise_68
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_equiv'45'raise_50)
