{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.Q1Z45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels

-- foundation-core.1-types.is-1-type
d_is'45'1'45'type_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'1'45'type_6 = erased
-- foundation-core.1-types.UU-1-Type
d_UU'45'1'45'Type_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_UU'45'1'45'Type_10 = erased
-- foundation-core.1-types.type-1-Type
d_type'45'1'45'Type_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'1'45'Type_16 = erased
-- foundation-core.1-types.is-1-type-type-1-Type
d_is'45'1'45'type'45'type'45'1'45'Type_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'1'45'type'45'type'45'1'45'Type_22 ~v0
  = du_is'45'1'45'type'45'type'45'1'45'Type_22
du_is'45'1'45'type'45'type'45'1'45'Type_22 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'1'45'type'45'type'45'1'45'Type_22
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
-- foundation-core.1-types.Id-Set
d_Id'45'Set_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Id'45'Set_32 ~v0 v1 v2 v3 = du_Id'45'Set_32 v1 v2 v3
du_Id'45'Set_32 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Id'45'Set_32 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'1'45'type'45'type'45'1'45'Type_22 v0 v1 v2)
-- foundation-core.1-types.1-type-Set
d_1'45'type'45'Set_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_1'45'type'45'Set_48 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.d_truncated'45'type'45'succ'45'Truncated'45'Type_72
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_zero'45'𝕋_12)
      (coe v0) (coe v1)
