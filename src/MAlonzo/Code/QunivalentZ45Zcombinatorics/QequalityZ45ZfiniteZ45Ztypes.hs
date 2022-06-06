{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZfiniteZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Zequality
import qualified MAlonzo.Code.Qfoundation.QmereZ45Zequivalences
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.Qsets
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QcountingZ45ZdecidableZ45Zsubtypes
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QfiniteZ45Ztypes

-- univalent-combinatorics.equality-finite-types.is-set-is-finite
d_is'45'set'45'is'45'finite_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'is'45'finite_8 v0 ~v1 v2
  = du_is'45'set'45'is'45'finite_8 v0 v2
du_is'45'set'45'is'45'finite_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'is'45'finite_8 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe v0) (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Qfoundation.Qsets.du_is'45'set'45'Prop_78 (coe v0))
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_is'45'set'45'count_32)
-- univalent-combinatorics.equality-finite-types.set-𝔽
d_set'45'𝔽_18 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_set'45'𝔽_18 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'set'45'is'45'finite_8 (coe ())
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QfiniteZ45Ztypes.d_is'45'finite'45'type'45'𝔽_38
            (coe v0)))
-- univalent-combinatorics.equality-finite-types.has-decidable-equality-is-finite
d_has'45'decidable'45'equality'45'is'45'finite_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'is'45'finite_28 v0 ~v1 v2
  = du_has'45'decidable'45'equality'45'is'45'finite_28 v0 v2
du_has'45'decidable'45'equality'45'is'45'finite_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'is'45'finite_28 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe v0) (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_has'45'decidable'45'equality'45'Prop_472
         (coe v0))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_has'45'decidable'45'equality'45'equiv''_284
              (coe
                 MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_equiv'45'count_24
                 (coe v2))
              (coe
                 MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes.du_has'45'decidable'45'equality'45'Fin_112)))
-- univalent-combinatorics.equality-finite-types.is-set-has-cardinality
d_is'45'set'45'has'45'cardinality_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'has'45'cardinality_44 v0 ~v1 v2 v3
  = du_is'45'set'45'has'45'cardinality_44 v0 v2 v3
du_is'45'set'45'has'45'cardinality_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'has'45'cardinality_44 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QmereZ45Zequivalences.du_is'45'set'45'mere'45'equiv''_144
      v0 v2
      (MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes.d_is'45'set'45'Fin_152
         (coe v1))
-- univalent-combinatorics.equality-finite-types.set-UU-Fin-Level
d_set'45'UU'45'Fin'45'Level_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_set'45'UU'45'Fin'45'Level_52 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'set'45'has'45'cardinality_44 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QfiniteZ45Ztypes.du_mere'45'equiv'45'UU'45'Fin'45'Level_80
            (coe v2)))
-- univalent-combinatorics.equality-finite-types.set-UU-Fin
d_set'45'UU'45'Fin_60 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_set'45'UU'45'Fin_60 v0 v1
  = coe d_set'45'UU'45'Fin'45'Level_52 (coe ()) (coe v0) (coe v1)
-- univalent-combinatorics.equality-finite-types.has-decidable-equality-has-cardinality
d_has'45'decidable'45'equality'45'has'45'cardinality_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'has'45'cardinality_70 v0 ~v1 ~v2
                                                        v3
  = du_has'45'decidable'45'equality'45'has'45'cardinality_70 v0 v3
du_has'45'decidable'45'equality'45'has'45'cardinality_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'has'45'cardinality_70 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe v0) (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_has'45'decidable'45'equality'45'Prop_472
         (coe v0))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_has'45'decidable'45'equality'45'equiv''_284
              v2
              (coe
                 MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes.du_has'45'decidable'45'equality'45'Fin_112)))
-- univalent-combinatorics.equality-finite-types.is-finite-eq
d_is'45'finite'45'eq_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'finite'45'eq_90 v0 ~v1 v2 v3 v4
  = du_is'45'finite'45'eq_90 v0 v2 v3 v4
du_is'45'finite'45'eq_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_is'45'finite'45'eq_90 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QunivalentZ45Zcombinatorics.QfiniteZ45Ztypes.du_is'45'finite'45'count_28
      v0
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.QcountingZ45ZdecidableZ45Zsubtypes.du_count'45'eq_78
         (coe v1) (coe v2) (coe v3))
-- univalent-combinatorics.equality-finite-types.Id-𝔽
d_Id'45'𝔽_104 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Id'45'𝔽_104 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'finite'45'eq_90 (coe ())
         (coe
            du_has'45'decidable'45'equality'45'is'45'finite_28 (coe ())
            (coe
               MAlonzo.Code.QunivalentZ45Zcombinatorics.QfiniteZ45Ztypes.d_is'45'finite'45'type'45'𝔽_38
               (coe v0)))
         (coe v1) (coe v2))
