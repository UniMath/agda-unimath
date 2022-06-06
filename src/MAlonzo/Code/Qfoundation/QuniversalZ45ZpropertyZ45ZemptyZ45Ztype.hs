{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZemptyZ45Ztype where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qequivalences

-- foundation.universal-property-empty-type._.dependent-universal-property-empty
d_dependent'45'universal'45'property'45'empty_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_dependent'45'universal'45'property'45'empty_14 = erased
-- foundation.universal-property-empty-type._.universal-property-empty
d_universal'45'property'45'empty_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_universal'45'property'45'empty_24 = erased
-- foundation.universal-property-empty-type._.universal-property-dependent-universal-property-empty
d_universal'45'property'45'dependent'45'universal'45'property'45'empty_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'dependent'45'universal'45'property'45'empty_34 ~v0
                                                                          ~v1 v2 v3 v4
  = du_universal'45'property'45'dependent'45'universal'45'property'45'empty_34
      v2 v3 v4
du_universal'45'property'45'dependent'45'universal'45'property'45'empty_34 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'dependent'45'universal'45'property'45'empty_34 v0
                                                                           v1 v2
  = coe v0 v1 (\ v3 -> v2)
-- foundation.universal-property-empty-type._.is-empty-universal-property-empty
d_is'45'empty'45'universal'45'property'45'empty_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'universal'45'property'45'empty_46 = erased
-- foundation.universal-property-empty-type._.dependent-universal-property-empty-is-empty
d_dependent'45'universal'45'property'45'empty'45'is'45'empty_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_dependent'45'universal'45'property'45'empty'45'is'45'empty_54 ~v0
                                                                ~v1 ~v2 ~v3 ~v4
  = du_dependent'45'universal'45'property'45'empty'45'is'45'empty_54
du_dependent'45'universal'45'property'45'empty'45'is'45'empty_54 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_dependent'45'universal'45'property'45'empty'45'is'45'empty_54
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
              erased))
      erased
-- foundation.universal-property-empty-type._.universal-property-empty-is-empty
d_universal'45'property'45'empty'45'is'45'empty_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'empty'45'is'45'empty_78 ~v0 ~v1 v2 ~v3
  = du_universal'45'property'45'empty'45'is'45'empty_78 v2
du_universal'45'property'45'empty'45'is'45'empty_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'empty'45'is'45'empty_78 v0
  = coe
      du_universal'45'property'45'dependent'45'universal'45'property'45'empty_34
      (coe
         (\ v1 v2 ->
            coe
              du_dependent'45'universal'45'property'45'empty'45'is'45'empty_54))
      (coe v0)
-- foundation.universal-property-empty-type.dependent-universal-property-empty'
d_dependent'45'universal'45'property'45'empty''_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_dependent'45'universal'45'property'45'empty''_90 ~v0 ~v1
  = du_dependent'45'universal'45'property'45'empty''_90
du_dependent'45'universal'45'property'45'empty''_90 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_dependent'45'universal'45'property'45'empty''_90
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (\ v0 ->
         coe
           MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ind'45'empty_12)
      erased
-- foundation.universal-property-empty-type.universal-property-empty'
d_universal'45'property'45'empty''_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'empty''_102 ~v0 ~v1
  = du_universal'45'property'45'empty''_102
du_universal'45'property'45'empty''_102 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'empty''_102
  = coe du_dependent'45'universal'45'property'45'empty''_90
-- foundation.universal-property-empty-type.uniqueness-empty
d_uniqueness'45'empty_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_uniqueness'45'empty_118 ~v0 ~v1 v2
  = du_uniqueness'45'empty_118 v2
du_uniqueness'45'empty_118 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_uniqueness'45'empty_118 v0
  = coe
      MAlonzo.Code.Qfoundation.Qequivalences.du_is'45'equiv'45'is'45'equiv'45'precomp_446
      (coe ()) erased
      (\ v1 ->
         coe
           MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ind'45'empty_12)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'equiv'45'is'45'contr_238
              (coe v0 v1 v2)))
-- foundation.universal-property-empty-type.universal-property-empty-is-equiv-ind-empty
d_universal'45'property'45'empty'45'is'45'equiv'45'ind'45'empty_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'empty'45'is'45'equiv'45'ind'45'empty_140 ~v0
                                                                    ~v1 v2 ~v3 ~v4
  = du_universal'45'property'45'empty'45'is'45'equiv'45'ind'45'empty_140
      v2
du_universal'45'property'45'empty'45'is'45'equiv'45'ind'45'empty_140 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'empty'45'is'45'equiv'45'ind'45'empty_140 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'is'45'equiv_162
      (coe
         MAlonzo.Code.Qfoundation.Qequivalences.du_is'45'equiv'45'precomp'45'is'45'equiv_360
         (\ v1 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ind'45'empty_12)
         v0 erased)
      (coe du_universal'45'property'45'empty''_102)
