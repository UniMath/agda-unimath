{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QunivalentZ45Zcombinatorics.QcountingZ45ZdecidableZ45Zsubtypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qembeddings
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QpropositionalZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Zequality
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZemptyZ45Ztype
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QfiniteZ45Ztypes
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes

-- univalent-combinatorics.counting-decidable-subtypes.is-decidable-count
d_is'45'decidable'45'count_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'count_8 ~v0 ~v1 v2
  = du_is'45'decidable'45'count_8 v2
du_is'45'decidable'45'count_8 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'count_8 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                       v2
                       (MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_zero'45'Fin_230
                          (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.counting-decidable-subtypes.count-is-decidable-is-prop
d_count'45'is'45'decidable'45'is'45'prop_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'is'45'decidable'45'is'45'prop_20 ~v0 ~v1 v2 v3
  = du_count'45'is'45'decidable'45'is'45'prop_20 v2 v3
du_count'45'is'45'decidable'45'is'45'prop_20 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'is'45'decidable'45'is'45'prop_20 v0 v1
  = case coe v1 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'is'45'contr_152
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
                v0 v2)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'is'45'empty_140
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.counting-decidable-subtypes.count-decidable-Prop
d_count'45'decidable'45'Prop_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'decidable'45'Prop_34 ~v0 v1 v2
  = du_count'45'decidable'45'Prop_34 v1 v2
du_count'45'decidable'45'Prop_34 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'decidable'45'Prop_34 v0 v1
  = case coe v1 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'is'45'contr_152
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
                (coe
                   MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
                   (coe v0))
                v2)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'is'45'empty_140
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.counting-decidable-subtypes.cases-count-eq
d_cases'45'count'45'eq_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cases'45'count'45'eq_56 ~v0 ~v1 ~v2 v3 v4 v5
  = du_cases'45'count'45'eq_56 v3 v4 v5
du_cases'45'count'45'eq_56 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_cases'45'count'45'eq_56 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
        -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'is'45'contr_152
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
                (coe
                   MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_is'45'set'45'has'45'decidable'45'equality_434
                   v0 v1)
                v3)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
        -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'is'45'empty_140
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.counting-decidable-subtypes.count-eq
d_count'45'eq_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'eq_78 ~v0 ~v1 v2 v3 v4 = du_count'45'eq_78 v2 v3 v4
du_count'45'eq_78 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'eq_78 v0 v1 v2
  = coe du_cases'45'count'45'eq_56 (coe v1) (coe v2) (coe v0 v1 v2)
-- univalent-combinatorics.counting-decidable-subtypes.cases-number-of-elements-count-eq'
d_cases'45'number'45'of'45'elements'45'count'45'eq''_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> Integer
d_cases'45'number'45'of'45'elements'45'count'45'eq''_94 ~v0 ~v1 ~v2
                                                        ~v3 v4
  = du_cases'45'number'45'of'45'elements'45'count'45'eq''_94 v4
du_cases'45'number'45'of'45'elements'45'count'45'eq''_94 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> Integer
du_cases'45'number'45'of'45'elements'45'count'45'eq''_94 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe (1 :: Integer)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.counting-decidable-subtypes.number-of-elements-count-eq'
d_number'45'of'45'elements'45'count'45'eq''_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny -> AgdaAny -> Integer
d_number'45'of'45'elements'45'count'45'eq''_110 ~v0 ~v1 v2 v3 v4
  = du_number'45'of'45'elements'45'count'45'eq''_110 v2 v3 v4
du_number'45'of'45'elements'45'count'45'eq''_110 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny -> AgdaAny -> Integer
du_number'45'of'45'elements'45'count'45'eq''_110 v0 v1 v2
  = coe
      du_cases'45'number'45'of'45'elements'45'count'45'eq''_94
      (coe v0 v1 v2)
-- univalent-combinatorics.counting-decidable-subtypes.cases-number-of-elements-count-eq
d_cases'45'number'45'of'45'elements'45'count'45'eq_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_cases'45'number'45'of'45'elements'45'count'45'eq_130 = erased
-- univalent-combinatorics.counting-decidable-subtypes.number-of-elements-count-eq
d_number'45'of'45'elements'45'count'45'eq_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_number'45'of'45'elements'45'count'45'eq_150 = erased
-- univalent-combinatorics.counting-decidable-subtypes.count-decidable-subtype'
d_count'45'decidable'45'subtype''_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'decidable'45'subtype''_172 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_count'45'decidable'45'subtype''_172 v3 v4 v5 v6
du_count'45'decidable'45'subtype''_172 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'decidable'45'subtype''_172 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'is'45'empty_140
             erased
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           let v5
                 = coe
                     v1
                     (coe
                        MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                        v3
                        (coe
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased)) in
           case coe v5 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v6
               -> coe
                    MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'equiv_64
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'Σ_544
                       (coe v3)
                       (coe
                          (\ v7 ->
                             coe
                               MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92)))
                    (coe
                       MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'equiv''_84
                       (coe
                          MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZcoproductZ45Ztypes.du_right'45'distributive'45'Σ'45'coprod_176)
                       (coe
                          MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_number'45'of'45'elements'45'count_22
                                (coe
                                   du_count'45'decidable'45'subtype''_172
                                   (coe
                                      (\ v7 ->
                                         coe
                                           v0
                                           (coe
                                              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                                              v3
                                              (coe
                                                 MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                                                 (coe v7)))))
                                   (coe
                                      (\ v7 ->
                                         coe
                                           v1
                                           (coe
                                              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                                              v3
                                              (coe
                                                 MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                                                 (coe v7)))))
                                   (coe v4)
                                   (coe
                                      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92))))
                          (coe
                             MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_equiv'45'coprod_242
                             (coe
                                MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_equiv'45'count_24
                                (coe
                                   du_count'45'decidable'45'subtype''_172
                                   (coe
                                      (\ v7 ->
                                         coe
                                           v0
                                           (coe
                                              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                                              v3
                                              (coe
                                                 MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                                                 (coe v7)))))
                                   (coe
                                      (\ v7 ->
                                         coe
                                           v1
                                           (coe
                                              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                                              v3
                                              (coe
                                                 MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                                                 (coe v7)))))
                                   (coe v4)
                                   (coe
                                      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92)))
                             (coe
                                MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_equiv'45'is'45'contr_250
                                (coe
                                   MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_is'45'contr'45'unit_42)
                                (coe
                                   MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'Σ_384
                                   erased
                                   (coe
                                      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
                                      (coe
                                         MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
                                         (coe
                                            v0
                                            (coe
                                               MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                                               v3
                                               (coe
                                                  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                                                  erased))))
                                      v6))))))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v6
               -> coe
                    MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'equiv_64
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'Σ_544
                       (coe v3)
                       (coe
                          (\ v7 ->
                             coe
                               MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92)))
                    (coe
                       MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'equiv''_84
                       (coe
                          MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZcoproductZ45Ztypes.du_right'45'distributive'45'Σ'45'coprod_176)
                       (coe
                          MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'equiv''_84
                          (coe
                             MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZemptyZ45Ztype.du_right'45'unit'45'law'45'coprod'45'is'45'empty_260)
                          (coe
                             du_count'45'decidable'45'subtype''_172
                             (coe
                                (\ v7 ->
                                   coe
                                     v0
                                     (coe
                                        MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                                        v3
                                        (coe
                                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                                           (coe v7)))))
                             (coe
                                (\ v7 ->
                                   coe
                                     v1
                                     (coe
                                        MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                                        v3
                                        (coe
                                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                                           (coe v7)))))
                             (coe v4)
                             (coe
                                MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92))))
             _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.counting-decidable-subtypes.count-decidable-subtype
d_count'45'decidable'45'subtype_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'decidable'45'subtype_256 ~v0 ~v1 ~v2 v3 v4 v5
  = du_count'45'decidable'45'subtype_256 v3 v4 v5
du_count'45'decidable'45'subtype_256 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'decidable'45'subtype_256 v0 v1 v2
  = coe
      du_count'45'decidable'45'subtype''_172 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_number'45'of'45'elements'45'count_22
         (coe v2))
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_equiv'45'count_24
         (coe v2))
-- univalent-combinatorics.counting-decidable-subtypes.is-decidable-count-subtype
d_is'45'decidable'45'count'45'subtype_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'count'45'subtype_274 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_is'45'decidable'45'count'45'subtype_274 v4 v5 v6
du_is'45'decidable'45'count'45'subtype_274 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'count'45'subtype_274 v0 v1 v2
  = coe
      du_is'45'decidable'45'count_8
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'equiv_64
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_equiv'45'fib'45'pr1_194
            (coe v2))
         (coe
            du_count'45'decidable'45'subtype_256
            (coe
               (\ v3 ->
                  coe
                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                    erased
                    (coe
                       MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_is'45'set'45'count_32
                       v0
                       (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                          (coe v3))
                       v2)))
            (coe
               (\ v3 ->
                  coe
                    MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_has'45'decidable'45'equality'45'count_196
                    v0
                    (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                       (coe v3))
                    v2))
            (coe v1)))
-- univalent-combinatorics.counting-decidable-subtypes.count-type-subtype-is-finite-type-subtype
d_count'45'type'45'subtype'45'is'45'finite'45'type'45'subtype_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'type'45'subtype'45'is'45'finite'45'type'45'subtype_298 ~v0
                                                                  v1 ~v2 v3 v4 v5
  = du_count'45'type'45'subtype'45'is'45'finite'45'type'45'subtype_298
      v1 v3 v4 v5
du_count'45'type'45'subtype'45'is'45'finite'45'type'45'subtype_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'type'45'subtype'45'is'45'finite'45'type'45'subtype_298 v0
                                                                   v1 v2 v3
  = coe
      du_count'45'decidable'45'subtype_256 (coe v2)
      (coe du_d_318 (coe v0) (coe v1) (coe v3)) (coe v1)
-- univalent-combinatorics.counting-decidable-subtypes._.d
d_d_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_d_318 ~v0 v1 ~v2 v3 ~v4 v5 v6 = du_d_318 v1 v3 v5 v6
du_d_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_d_318 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe ()) (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'Prop_406)
      (coe
         (\ v4 ->
            coe
              du_is'45'decidable'45'count'45'subtype_274 (coe v1) (coe v4)
              (coe v3)))
-- univalent-combinatorics.counting-decidable-subtypes.count-domain-emb-is-finite-domain-emb
d_count'45'domain'45'emb'45'is'45'finite'45'domain'45'emb_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'domain'45'emb'45'is'45'finite'45'domain'45'emb_336 ~v0
                                                              v1 ~v2 v3 ~v4 v5 v6
  = du_count'45'domain'45'emb'45'is'45'finite'45'domain'45'emb_336
      v1 v3 v5 v6
du_count'45'domain'45'emb'45'is'45'finite'45'domain'45'emb_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'domain'45'emb'45'is'45'finite'45'domain'45'emb_336 v0
                                                               v1 v2 v3
  = coe
      MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'equiv_64
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_equiv'45'total'45'fib_238
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qembeddings.du_map'45'emb_46
            (coe v2)))
      (coe
         du_count'45'type'45'subtype'45'is'45'finite'45'type'45'subtype_298
         (coe ()) (coe v1)
         (coe
            (\ v4 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                 erased
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.QpropositionalZ45Zmaps.du_is'45'prop'45'map'45'emb_80
                    v4)))
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QfiniteZ45Ztypes.du_is'45'finite'45'equiv''_162
            () v0
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_equiv'45'total'45'fib_238
               (coe
                  MAlonzo.Code.QfoundationZ45Zcore.Qembeddings.du_map'45'emb_46
                  (coe v2)))
            v3))
