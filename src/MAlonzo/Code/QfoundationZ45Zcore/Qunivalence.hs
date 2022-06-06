{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.Qunivalence where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes

-- foundation-core.univalence.equiv-eq
d_equiv'45'eq_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'eq_10 ~v0 ~v1 ~v2 ~v3 = du_equiv'45'eq_10
du_equiv'45'eq_10 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'eq_10
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92
-- foundation-core.univalence.UNIVALENCE
d_UNIVALENCE_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> () -> ()
d_UNIVALENCE_18 = erased
-- foundation-core.univalence.is-contr-total-equiv-UNIVALENCE
d_is'45'contr'45'total'45'equiv'45'UNIVALENCE_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (() ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'equiv'45'UNIVALENCE_32 ~v0 v1 ~v2
  = du_is'45'contr'45'total'45'equiv'45'UNIVALENCE_32 v1
du_is'45'contr'45'total'45'equiv'45'UNIVALENCE_32 ::
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'equiv'45'UNIVALENCE_32 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id''_34
      (coe v0) (coe (\ v1 v2 -> coe du_equiv'45'eq_10))
-- foundation-core.univalence.UNIVALENCE-is-contr-total-equiv
d_UNIVALENCE'45'is'45'contr'45'total'45'equiv_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_UNIVALENCE'45'is'45'contr'45'total'45'equiv_48 ~v0 v1 ~v2
  = du_UNIVALENCE'45'is'45'contr'45'total'45'equiv_48 v1
du_UNIVALENCE'45'is'45'contr'45'total'45'equiv_48 ::
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_UNIVALENCE'45'is'45'contr'45'total'45'equiv_48 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation-core.univalence.tr-equiv-eq-ap
d_tr'45'equiv'45'eq'45'ap_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_tr'45'equiv'45'eq'45'ap_70 = erased
