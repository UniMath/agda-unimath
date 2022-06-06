{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QmereZ45Zequality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZpropositionalZ45Ztruncation
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations

-- foundation.mere-equality.mere-eq-Prop
d_mere'45'eq'45'Prop_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_mere'45'eq'45'Prop_8 v0 ~v1 ~v2 ~v3 = du_mere'45'eq'45'Prop_8 v0
du_mere'45'eq'45'Prop_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_mere'45'eq'45'Prop_8 v0
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
      v0 erased
-- foundation.mere-equality.mere-eq
d_mere'45'eq_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> AgdaAny -> ()
d_mere'45'eq_18 = erased
-- foundation.mere-equality.refl-mere-eq
d_refl'45'mere'45'eq_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> AgdaAny
d_refl'45'mere'45'eq_30 v0 ~v1 ~v2 = du_refl'45'mere'45'eq_30 v0
du_refl'45'mere'45'eq_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny
du_refl'45'mere'45'eq_30 v0
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
      v0 erased
-- foundation.mere-equality.symm-mere-eq
d_symm'45'mere'45'eq_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_symm'45'mere'45'eq_40 v0 ~v1 ~v2 ~v3
  = du_symm'45'mere'45'eq_40 v0
du_symm'45'mere'45'eq_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny -> AgdaAny
du_symm'45'mere'45'eq_40 v0
  = coe
      MAlonzo.Code.Qfoundation.QfunctorialityZ45ZpropositionalZ45Ztruncation.du_functor'45'trunc'45'Prop_36
      (coe v0) (coe v0) erased
-- foundation.mere-equality.trans-mere-eq
d_trans'45'mere'45'eq_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'45'mere'45'eq_56 v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_trans'45'mere'45'eq_56 v0 v5 v6
du_trans'45'mere'45'eq_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_trans'45'mere'45'eq_56 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe v0) (coe v0) (coe v1) (coe du_mere'45'eq'45'Prop_8 (coe v0))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Qfoundation.QfunctorialityZ45ZpropositionalZ45Ztruncation.du_functor'45'trunc'45'Prop_36
              v0 v0 erased v2))
-- foundation.mere-equality.mere-eq-Eq-Rel
d_mere'45'eq'45'Eq'45'Rel_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_mere'45'eq'45'Eq'45'Rel_76 v0 ~v1
  = du_mere'45'eq'45'Eq'45'Rel_76 v0
du_mere'45'eq'45'Eq'45'Rel_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_mere'45'eq'45'Eq'45'Rel_76 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (\ v1 v2 -> coe du_mere'45'eq'45'Prop_8 (coe v0))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe (\ v1 -> coe du_refl'45'mere'45'eq_30 (coe v0)))
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
            (coe (\ v1 v2 -> coe du_symm'45'mere'45'eq_40 (coe v0)))
            (coe (\ v1 v2 v3 -> coe du_trans'45'mere'45'eq_56 (coe v0)))))
-- foundation.mere-equality._.reflects-mere-eq
d_reflects'45'mere'45'eq_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_reflects'45'mere'45'eq_100 = erased
-- foundation.mere-equality._.reflecting-map-mere-eq
d_reflecting'45'map'45'mere'45'eq_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_reflecting'45'map'45'mere'45'eq_108 ~v0 ~v1 ~v2 ~v3 v4
  = du_reflecting'45'map'45'mere'45'eq_108 v4
du_reflecting'45'map'45'mere'45'eq_108 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_reflecting'45'map'45'mere'45'eq_108 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe v0) erased
