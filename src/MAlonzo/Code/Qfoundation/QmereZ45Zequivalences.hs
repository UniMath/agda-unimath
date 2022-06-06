{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QmereZ45Zequivalences where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Zequality
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZpropositionalZ45Ztruncation
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes

-- foundation.mere-equivalences.mere-equiv-Prop
d_mere'45'equiv'45'Prop_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_mere'45'equiv'45'Prop_8 ~v0 ~v1 ~v2 ~v3
  = du_mere'45'equiv'45'Prop_8
du_mere'45'equiv'45'Prop_8 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_mere'45'equiv'45'Prop_8
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
      () erased
-- foundation.mere-equivalences.mere-equiv
d_mere'45'equiv_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> () -> ()
d_mere'45'equiv_18 = erased
-- foundation.mere-equivalences.is-prop-mere-equiv
d_is'45'prop'45'mere'45'equiv_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'mere'45'equiv_32 ~v0 ~v1 ~v2 ~v3
  = du_is'45'prop'45'mere'45'equiv_32
du_is'45'prop'45'mere'45'equiv_32 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'mere'45'equiv_32
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
      (coe du_mere'45'equiv'45'Prop_8)
-- foundation.mere-equivalences.refl-mere-equiv
d_refl'45'mere'45'equiv_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny
d_refl'45'mere'45'equiv_42 v0 ~v1 = du_refl'45'mere'45'equiv_42 v0
du_refl'45'mere'45'equiv_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny
du_refl'45'mere'45'equiv_42 v0
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
      v0
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92)
-- foundation.mere-equivalences.symmetric-mere-equiv
d_symmetric'45'mere'45'equiv_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> AgdaAny -> AgdaAny
d_symmetric'45'mere'45'equiv_54 ~v0 ~v1 ~v2 ~v3
  = du_symmetric'45'mere'45'equiv_54
du_symmetric'45'mere'45'equiv_54 :: AgdaAny -> AgdaAny
du_symmetric'45'mere'45'equiv_54
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_map'45'universal'45'property'45'trunc'45'Prop_176
      (coe ()) (coe ()) (coe du_mere'45'equiv'45'Prop_8)
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
              ()
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
                 (coe v0))))
-- foundation.mere-equivalences.transitive-mere-equiv
d_transitive'45'mere'45'equiv_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_transitive'45'mere'45'equiv_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_transitive'45'mere'45'equiv_78 v6 v7
du_transitive'45'mere'45'equiv_78 :: AgdaAny -> AgdaAny -> AgdaAny
du_transitive'45'mere'45'equiv_78 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe ()) (coe ()) (coe v0) (coe du_mere'45'equiv'45'Prop_8)
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
              (coe ()) (coe ()) (coe v1) (coe du_mere'45'equiv'45'Prop_8)
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
                      ()
                      (coe
                         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386 v3
                         v2)))))
-- foundation.mere-equivalences._.is-trunc-mere-equiv
d_is'45'trunc'45'mere'45'equiv_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'mere'45'equiv_108 v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_is'45'trunc'45'mere'45'equiv_108 v0 v4 v5 v6
du_is'45'trunc'45'mere'45'equiv_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'mere'45'equiv_108 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe ()) (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes.du_is'45'trunc'45'Prop_258
         (coe v0) (coe v1))
      (coe
         (\ v4 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'equiv_206
              v1 v4 v3))
-- foundation.mere-equivalences._.is-trunc-mere-equiv'
d_is'45'trunc'45'mere'45'equiv''_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'mere'45'equiv''_120 ~v0 v1 ~v2 ~v3 v4 v5 v6
  = du_is'45'trunc'45'mere'45'equiv''_120 v1 v4 v5 v6
du_is'45'trunc'45'mere'45'equiv''_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'mere'45'equiv''_120 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe ()) (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes.du_is'45'trunc'45'Prop_258
         (coe v0) (coe v1))
      (coe
         (\ v4 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'equiv''_252
              v1 v4 v3))
-- foundation.mere-equivalences._.is-set-mere-equiv
d_is'45'set'45'mere'45'equiv_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'mere'45'equiv_142 v0 ~v1 ~v2 ~v3
  = du_is'45'set'45'mere'45'equiv_142 v0
du_is'45'set'45'mere'45'equiv_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'mere'45'equiv_142 v0
  = coe
      du_is'45'trunc'45'mere'45'equiv_108 (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_zero'45'𝕋_12)
-- foundation.mere-equivalences._.is-set-mere-equiv'
d_is'45'set'45'mere'45'equiv''_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'mere'45'equiv''_144 ~v0 v1 ~v2 ~v3
  = du_is'45'set'45'mere'45'equiv''_144 v1
du_is'45'set'45'mere'45'equiv''_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'mere'45'equiv''_144 v0
  = coe
      du_is'45'trunc'45'mere'45'equiv''_120 (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_zero'45'𝕋_12)
-- foundation.mere-equivalences._.has-decidable-equality-mere-equiv
d_has'45'decidable'45'equality'45'mere'45'equiv_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'mere'45'equiv_158 v0 ~v1 ~v2 ~v3
                                                    v4 v5
  = du_has'45'decidable'45'equality'45'mere'45'equiv_158 v0 v4 v5
du_has'45'decidable'45'equality'45'mere'45'equiv_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'mere'45'equiv_158 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe ()) (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_has'45'decidable'45'equality'45'Prop_472
         (coe v0))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_has'45'decidable'45'equality'45'equiv_264
              (coe v3) (coe v2)))
-- foundation.mere-equivalences._.has-decidable-equality-mere-equiv'
d_has'45'decidable'45'equality'45'mere'45'equiv''_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'mere'45'equiv''_166 ~v0 v1 ~v2
                                                      ~v3 v4 v5
  = du_has'45'decidable'45'equality'45'mere'45'equiv''_166 v1 v4 v5
du_has'45'decidable'45'equality'45'mere'45'equiv''_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'mere'45'equiv''_166 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe ()) (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_has'45'decidable'45'equality'45'Prop_472
         (coe v0))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_has'45'decidable'45'equality'45'equiv''_284
              v3 v2))
-- foundation.mere-equivalences.mere-eq-mere-equiv
d_mere'45'eq'45'mere'45'equiv_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> AgdaAny -> AgdaAny
d_mere'45'eq'45'mere'45'equiv_180 v0 ~v1 ~v2
  = du_mere'45'eq'45'mere'45'equiv_180 v0
du_mere'45'eq'45'mere'45'equiv_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny -> AgdaAny
du_mere'45'eq'45'mere'45'equiv_180 v0
  = coe
      MAlonzo.Code.Qfoundation.QfunctorialityZ45ZpropositionalZ45Ztruncation.du_functor'45'trunc'45'Prop_36
      (coe v0) (coe ()) erased
