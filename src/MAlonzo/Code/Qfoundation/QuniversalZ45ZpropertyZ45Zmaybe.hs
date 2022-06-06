{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45Zmaybe where

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
import qualified MAlonzo.Code.Qfoundation.Qmaybe

-- foundation.universal-property-maybe._.ev-Maybe
d_ev'45'Maybe_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_ev'45'Maybe_20 ~v0 ~v1 ~v2 ~v3 v4 = du_ev'45'Maybe_20 v4
du_ev'45'Maybe_20 ::
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_ev'45'Maybe_20 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         (\ v1 ->
            coe
              v0 (coe MAlonzo.Code.Qfoundation.Qmaybe.du_unit'45'Maybe_14 v1)))
      (coe
         v0 (coe MAlonzo.Code.Qfoundation.Qmaybe.du_exception'45'Maybe_20))
-- foundation.universal-property-maybe._.ind-Maybe
d_ind'45'Maybe_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_ind'45'Maybe_32 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_ind'45'Maybe_32 v4 v5
du_ind'45'Maybe_32 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
du_ind'45'Maybe_32 v0 v1
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
               -> coe v2 v4
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.universal-property-maybe._.issec-ind-Maybe
d_issec'45'ind'45'Maybe_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'ind'45'Maybe_44 = erased
-- foundation.universal-property-maybe._.isretr-ind-Maybe'
d_isretr'45'ind'45'Maybe''_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   AgdaAny) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'ind'45'Maybe''_54 = erased
-- foundation.universal-property-maybe._.isretr-ind-Maybe
d_isretr'45'ind'45'Maybe_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'ind'45'Maybe_62 = erased
-- foundation.universal-property-maybe._.dependent-universal-property-Maybe
d_dependent'45'universal'45'property'45'Maybe_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_dependent'45'universal'45'property'45'Maybe_66 ~v0 ~v1 ~v2 ~v3
  = du_dependent'45'universal'45'property'45'Maybe_66
du_dependent'45'universal'45'property'45'Maybe_66 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_dependent'45'universal'45'property'45'Maybe_66
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_ind'45'Maybe_32) erased erased
-- foundation.universal-property-maybe.equiv-dependent-universal-property-Maybe
d_equiv'45'dependent'45'universal'45'property'45'Maybe_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'dependent'45'universal'45'property'45'Maybe_80 ~v0 ~v1
                                                          ~v2 ~v3
  = du_equiv'45'dependent'45'universal'45'property'45'Maybe_80
du_equiv'45'dependent'45'universal'45'property'45'Maybe_80 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'dependent'45'universal'45'property'45'Maybe_80
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_ev'45'Maybe_20)
      (coe du_dependent'45'universal'45'property'45'Maybe_66)
-- foundation.universal-property-maybe.equiv-universal-property-Maybe
d_equiv'45'universal'45'property'45'Maybe_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'universal'45'property'45'Maybe_94 ~v0 ~v1 ~v2 ~v3
  = du_equiv'45'universal'45'property'45'Maybe_94
du_equiv'45'universal'45'property'45'Maybe_94 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'universal'45'property'45'Maybe_94
  = coe du_equiv'45'dependent'45'universal'45'property'45'Maybe_80
