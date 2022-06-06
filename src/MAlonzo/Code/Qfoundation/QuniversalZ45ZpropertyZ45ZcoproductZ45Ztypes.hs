{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZcoproductZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qequivalences

-- foundation.universal-property-coproduct-types._.ev-inl-inr
d_ev'45'inl'45'inr_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_ev'45'inl'45'inr_26 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_ev'45'inl'45'inr_26 v6
du_ev'45'inl'45'inr_26 ::
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_ev'45'inl'45'inr_26 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         (\ v1 ->
            coe
              v0
              (coe
                 MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v1))))
      (coe
         (\ v1 ->
            coe
              v0
              (coe
                 MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v1))))
-- foundation.universal-property-coproduct-types._.dependent-universal-property-coprod
d_dependent'45'universal'45'property'45'coprod_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_dependent'45'universal'45'property'45'coprod_40 ~v0 ~v1 ~v2 ~v3
                                                  ~v4 ~v5
  = du_dependent'45'universal'45'property'45'coprod_40
du_dependent'45'universal'45'property'45'coprod_40 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_dependent'45'universal'45'property'45'coprod_40
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.du_ind'45'coprod_44
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                 (coe v0))
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
                 (coe v0))))
      erased erased
-- foundation.universal-property-coproduct-types._.equiv-dependent-universal-property-coprod
d_equiv'45'dependent'45'universal'45'property'45'coprod_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'dependent'45'universal'45'property'45'coprod_66 ~v0 ~v1
                                                           ~v2 ~v3 ~v4 ~v5
  = du_equiv'45'dependent'45'universal'45'property'45'coprod_66
du_equiv'45'dependent'45'universal'45'property'45'coprod_66 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'dependent'45'universal'45'property'45'coprod_66
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_ev'45'inl'45'inr_26)
      (coe du_dependent'45'universal'45'property'45'coprod_40)
-- foundation.universal-property-coproduct-types._.universal-property-coprod
d_universal'45'property'45'coprod_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'coprod_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_universal'45'property'45'coprod_78
du_universal'45'property'45'coprod_78 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'coprod_78
  = coe du_dependent'45'universal'45'property'45'coprod_40
-- foundation.universal-property-coproduct-types._.equiv-universal-property-coprod
d_equiv'45'universal'45'property'45'coprod_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'universal'45'property'45'coprod_88 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5
  = du_equiv'45'universal'45'property'45'coprod_88
du_equiv'45'universal'45'property'45'coprod_88 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'universal'45'property'45'coprod_88
  = coe du_equiv'45'dependent'45'universal'45'property'45'coprod_66
-- foundation.universal-property-coproduct-types._.uniqueness-coprod
d_uniqueness'45'coprod_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_uniqueness'45'coprod_110 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_uniqueness'45'coprod_110 v6 v7 v8
du_uniqueness'45'coprod_110 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_uniqueness'45'coprod_110 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.Qequivalences.du_is'45'equiv'45'is'45'equiv'45'precomp_446
      (coe ()) erased
      (coe
         MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.du_ind'45'coprod_44
         (coe v0) (coe v1))
      (coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'right'45'factor''_510
              (coe du_ev'45'inl'45'inr_26)
              (coe du_universal'45'property'45'coprod_78) (coe v2 v3 v4)))
-- foundation.universal-property-coproduct-types._.universal-property-coprod-is-equiv-ind-coprod
d_universal'45'property'45'coprod'45'is'45'equiv'45'ind'45'coprod_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'coprod'45'is'45'equiv'45'ind'45'coprod_144 ~v0
                                                                      ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
                                                                      ~v9 ~v10
  = du_universal'45'property'45'coprod'45'is'45'equiv'45'ind'45'coprod_144
      v6 v7 v8
du_universal'45'property'45'coprod'45'is'45'equiv'45'ind'45'coprod_144 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'coprod'45'is'45'equiv'45'ind'45'coprod_144 v0
                                                                       v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp_332
      (coe
         MAlonzo.Code.Qfoundation.Qequivalences.du_is'45'equiv'45'precomp'45'is'45'equiv_360
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.du_ind'45'coprod_44
            (coe v0) (coe v1))
         v2 erased)
      (coe du_universal'45'property'45'coprod_78)
