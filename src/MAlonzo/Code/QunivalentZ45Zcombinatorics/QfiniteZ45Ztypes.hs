{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QunivalentZ45Zcombinatorics.QfiniteZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QconnectedZ45ZcomponentsZ45Zuniverses
import qualified MAlonzo.Code.Qfoundation.QconnectedZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZpropositionalZ45Ztruncation
import qualified MAlonzo.Code.Qfoundation.QmereZ45Zequivalences
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZemptyZ45Ztype
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes

-- univalent-combinatorics.finite-types.is-finite-Prop
d_is'45'finite'45'Prop_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'finite'45'Prop_6 v0 ~v1 = du_is'45'finite'45'Prop_6 v0
du_is'45'finite'45'Prop_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'finite'45'Prop_6 v0
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
      v0 erased
-- univalent-combinatorics.finite-types.is-finite
d_is'45'finite_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'finite_12 = erased
-- univalent-combinatorics.finite-types.is-prop-is-finite
d_is'45'prop'45'is'45'finite_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'finite_20 v0 ~v1
  = du_is'45'prop'45'is'45'finite_20 v0
du_is'45'prop'45'is'45'finite_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'finite_20 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
      (coe du_is'45'finite'45'Prop_6 (coe v0))
-- univalent-combinatorics.finite-types.is-finite-count
d_is'45'finite'45'count_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'finite'45'count_28 v0 ~v1 = du_is'45'finite'45'count_28 v0
du_is'45'finite'45'count_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_is'45'finite'45'count_28 v0
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
      (coe v0)
-- univalent-combinatorics.finite-types.𝔽
d_𝔽_30 :: ()
d_𝔽_30 = erased
-- univalent-combinatorics.finite-types.type-𝔽
d_type'45'𝔽_32 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'𝔽_32 = erased
-- univalent-combinatorics.finite-types.is-finite-type-𝔽
d_is'45'finite'45'type'45'𝔽_38 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'finite'45'type'45'𝔽_38 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe v0)
-- univalent-combinatorics.finite-types.has-cardinality-Prop
d_has'45'cardinality'45'Prop_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_has'45'cardinality'45'Prop_44 ~v0 ~v1 ~v2
  = du_has'45'cardinality'45'Prop_44
du_has'45'cardinality'45'Prop_44 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_has'45'cardinality'45'Prop_44
  = coe
      MAlonzo.Code.Qfoundation.QmereZ45Zequivalences.du_mere'45'equiv'45'Prop_8
-- univalent-combinatorics.finite-types.has-cardinality
d_has'45'cardinality_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> Integer -> () -> ()
d_has'45'cardinality_52 = erased
-- univalent-combinatorics.finite-types.UU-Fin-Level
d_UU'45'Fin'45'Level_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> Integer -> ()
d_UU'45'Fin'45'Level_60 = erased
-- univalent-combinatorics.finite-types.type-UU-Fin-Level
d_type'45'UU'45'Fin'45'Level_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'UU'45'Fin'45'Level_70 = erased
-- univalent-combinatorics.finite-types.mere-equiv-UU-Fin-Level
d_mere'45'equiv'45'UU'45'Fin'45'Level_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_mere'45'equiv'45'UU'45'Fin'45'Level_80 ~v0 ~v1 v2
  = du_mere'45'equiv'45'UU'45'Fin'45'Level_80 v2
du_mere'45'equiv'45'UU'45'Fin'45'Level_80 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_mere'45'equiv'45'UU'45'Fin'45'Level_80 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe v0)
-- univalent-combinatorics.finite-types.UU-Fin
d_UU'45'Fin_84 :: Integer -> ()
d_UU'45'Fin_84 = erased
-- univalent-combinatorics.finite-types.type-UU-Fin
d_type'45'UU'45'Fin_90 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'UU'45'Fin_90 = erased
-- univalent-combinatorics.finite-types.mere-equiv-UU-Fin
d_mere'45'equiv'45'UU'45'Fin_98 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_mere'45'equiv'45'UU'45'Fin_98 ~v0 v1
  = du_mere'45'equiv'45'UU'45'Fin_98 v1
du_mere'45'equiv'45'UU'45'Fin_98 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_mere'45'equiv'45'UU'45'Fin_98 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe v0)
-- univalent-combinatorics.finite-types.has-finite-cardinality
d_has'45'finite'45'cardinality_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_has'45'finite'45'cardinality_104 = erased
-- univalent-combinatorics.finite-types.number-of-elements-has-finite-cardinality
d_number'45'of'45'elements'45'has'45'finite'45'cardinality_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  Integer
d_number'45'of'45'elements'45'has'45'finite'45'cardinality_114 ~v0
                                                               ~v1
  = du_number'45'of'45'elements'45'has'45'finite'45'cardinality_114
du_number'45'of'45'elements'45'has'45'finite'45'cardinality_114 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  Integer
du_number'45'of'45'elements'45'has'45'finite'45'cardinality_114
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
-- univalent-combinatorics.finite-types.mere-equiv-has-finite-cardinality
d_mere'45'equiv'45'has'45'finite'45'cardinality_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_mere'45'equiv'45'has'45'finite'45'cardinality_122 ~v0 ~v1
  = du_mere'45'equiv'45'has'45'finite'45'cardinality_122
du_mere'45'equiv'45'has'45'finite'45'cardinality_122 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_mere'45'equiv'45'has'45'finite'45'cardinality_122
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
-- univalent-combinatorics.finite-types.is-finite-equiv
d_is'45'finite'45'equiv_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_is'45'finite'45'equiv_134 v0 v1 ~v2 ~v3 v4
  = du_is'45'finite'45'equiv_134 v0 v1 v4
du_is'45'finite'45'equiv_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_is'45'finite'45'equiv_134 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_map'45'universal'45'property'45'trunc'45'Prop_176
      (coe v0) (coe v1) (coe du_is'45'finite'45'Prop_6 (coe v1))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
         (coe (\ v3 -> coe du_is'45'finite'45'count_28 (coe v1)))
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'equiv_64
            (coe v2)))
-- univalent-combinatorics.finite-types.is-finite-is-equiv
d_is'45'finite'45'is'45'equiv_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_is'45'finite'45'is'45'equiv_148 v0 v1 ~v2 ~v3 v4 v5
  = du_is'45'finite'45'is'45'equiv_148 v0 v1 v4 v5
du_is'45'finite'45'is'45'equiv_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_is'45'finite'45'is'45'equiv_148 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_map'45'universal'45'property'45'trunc'45'Prop_176
      (coe v0) (coe v1) (coe du_is'45'finite'45'Prop_6 (coe v1))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
         (coe (\ v4 -> coe du_is'45'finite'45'count_28 (coe v1)))
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'equiv_64
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
               (coe v2) (coe v3))))
-- univalent-combinatorics.finite-types.is-finite-equiv'
d_is'45'finite'45'equiv''_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_is'45'finite'45'equiv''_162 v0 v1 ~v2 ~v3 v4
  = du_is'45'finite'45'equiv''_162 v0 v1 v4
du_is'45'finite'45'equiv''_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_is'45'finite'45'equiv''_162 v0 v1 v2
  = coe
      du_is'45'finite'45'equiv_134 (coe v1) (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
         (coe v2))
-- univalent-combinatorics.finite-types.is-finite-mere-equiv
d_is'45'finite'45'mere'45'equiv_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_is'45'finite'45'mere'45'equiv_174 v0 v1 ~v2 ~v3 v4 v5
  = du_is'45'finite'45'mere'45'equiv_174 v0 v1 v4 v5
du_is'45'finite'45'mere'45'equiv_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_is'45'finite'45'mere'45'equiv_174 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe ()) (coe v1) (coe v2) (coe du_is'45'finite'45'Prop_6 (coe v1))
      (coe (\ v4 -> coe du_is'45'finite'45'equiv_134 v0 v1 v4 v3))
-- univalent-combinatorics.finite-types.is-finite-empty
d_is'45'finite'45'empty_182 :: AgdaAny
d_is'45'finite'45'empty_182
  = coe
      du_is'45'finite'45'count_28 ()
      MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.d_count'45'empty_146
-- univalent-combinatorics.finite-types.empty-𝔽
d_empty'45'𝔽_184 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_empty'45'𝔽_184
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'finite'45'empty_182)
-- univalent-combinatorics.finite-types.empty-UU-Fin
d_empty'45'UU'45'Fin_186 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_empty'45'UU'45'Fin_186
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
         MAlonzo.Code.Agda.Primitive.d_lzero_16
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92))
-- univalent-combinatorics.finite-types.has-finite-cardinality-empty
d_has'45'finite'45'cardinality'45'empty_188 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_has'45'finite'45'cardinality'45'empty_188
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
         ()
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92))
-- univalent-combinatorics.finite-types.is-finite-is-empty
d_is'45'finite'45'is'45'empty_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny
d_is'45'finite'45'is'45'empty_194 v0 ~v1 ~v2
  = du_is'45'finite'45'is'45'empty_194 v0
du_is'45'finite'45'is'45'empty_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny
du_is'45'finite'45'is'45'empty_194 v0
  = coe
      du_is'45'finite'45'count_28 v0
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'is'45'empty_140
         erased)
-- univalent-combinatorics.finite-types.has-finite-cardinality-is-empty
d_has'45'finite'45'cardinality'45'is'45'empty_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_has'45'finite'45'cardinality'45'is'45'empty_202 v0 ~v1 ~v2
  = du_has'45'finite'45'cardinality'45'is'45'empty_202 v0
du_has'45'finite'45'cardinality'45'is'45'empty_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_has'45'finite'45'cardinality'45'is'45'empty_202 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
         v0
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_equiv'45'count_24
            (coe
               MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'is'45'empty_140
               erased)))
-- univalent-combinatorics.finite-types.is-finite-unit
d_is'45'finite'45'unit_208 :: AgdaAny
d_is'45'finite'45'unit_208
  = coe
      du_is'45'finite'45'count_28 ()
      MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.d_count'45'unit_190
-- univalent-combinatorics.finite-types.unit-𝔽
d_unit'45'𝔽_210 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_unit'45'𝔽_210
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'finite'45'unit_208)
-- univalent-combinatorics.finite-types.unit-UU-Fin
d_unit'45'UU'45'Fin_212 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_unit'45'UU'45'Fin_212
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
         ()
         (coe
            MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZemptyZ45Ztype.du_left'45'unit'45'law'45'coprod_220))
-- univalent-combinatorics.finite-types.is-finite-is-contr
d_is'45'finite'45'is'45'contr_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'finite'45'is'45'contr_218 v0 ~v1 v2
  = du_is'45'finite'45'is'45'contr_218 v0 v2
du_is'45'finite'45'is'45'contr_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_is'45'finite'45'is'45'contr_218 v0 v1
  = coe
      du_is'45'finite'45'count_28 v0
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'is'45'contr_152
         (coe v1))
-- univalent-combinatorics.finite-types.is-finite-is-decidable-Prop
d_is'45'finite'45'is'45'decidable'45'Prop_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_is'45'finite'45'is'45'decidable'45'Prop_226 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
        -> coe
             du_is'45'finite'45'is'45'contr_218 (coe v0)
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
                (coe
                   MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
                   (coe v1))
                v3)
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
        -> coe du_is'45'finite'45'is'45'empty_194 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.finite-types.is-finite-Fin
d_is'45'finite'45'Fin_238 :: Integer -> AgdaAny
d_is'45'finite'45'Fin_238 v0
  = coe
      du_is'45'finite'45'count_28 ()
      (MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.d_count'45'Fin_36
         (coe v0))
-- univalent-combinatorics.finite-types.Fin-𝔽
d_Fin'45'𝔽_242 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Fin'45'𝔽_242 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'finite'45'Fin_238 (coe v0))
-- univalent-combinatorics.finite-types.Fin-UU-Fin
d_Fin'45'UU'45'Fin_250 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Fin'45'UU'45'Fin_250 ~v0 = du_Fin'45'UU'45'Fin_250
du_Fin'45'UU'45'Fin_250 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Fin'45'UU'45'Fin_250
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
         MAlonzo.Code.Agda.Primitive.d_lzero_16
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92))
-- univalent-combinatorics.finite-types.Fin-UU-Fin-Level
d_Fin'45'UU'45'Fin'45'Level_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Fin'45'UU'45'Fin'45'Level_260 v0 ~v1
  = du_Fin'45'UU'45'Fin'45'Level_260 v0
du_Fin'45'UU'45'Fin'45'Level_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Fin'45'UU'45'Fin'45'Level_260 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
         v0
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.du_equiv'45'raise'45'Fin_78))
-- univalent-combinatorics.finite-types.is-finite-ℤ-Mod
d_is'45'finite'45'ℤ'45'Mod_272 ::
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny
d_is'45'finite'45'ℤ'45'Mod_272 v0 ~v1
  = du_is'45'finite'45'ℤ'45'Mod_272 v0
du_is'45'finite'45'ℤ'45'Mod_272 :: Integer -> AgdaAny
du_is'45'finite'45'ℤ'45'Mod_272 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
             erased
      _ -> coe d_is'45'finite'45'Fin_238 (coe v0)
-- univalent-combinatorics.finite-types.ℤ-Mod-𝔽
d_ℤ'45'Mod'45'𝔽_282 ::
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_ℤ'45'Mod'45'𝔽_282 v0 ~v1 = du_ℤ'45'Mod'45'𝔽_282 v0
du_ℤ'45'Mod'45'𝔽_282 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_ℤ'45'Mod'45'𝔽_282 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'finite'45'ℤ'45'Mod_272 (coe v0))
-- univalent-combinatorics.finite-types.is-finite-type-UU-Fin-Level
d_is'45'finite'45'type'45'UU'45'Fin'45'Level_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'finite'45'type'45'UU'45'Fin'45'Level_298 v0 v1 v2
  = coe
      du_is'45'finite'45'mere'45'equiv_174 (coe ()) (coe v0)
      (coe du_mere'45'equiv'45'UU'45'Fin'45'Level_80 (coe v2))
      (coe d_is'45'finite'45'Fin_238 (coe v1))
-- univalent-combinatorics.finite-types.is-finite-type-UU-Fin
d_is'45'finite'45'type'45'UU'45'Fin_306 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'finite'45'type'45'UU'45'Fin_306 v0 v1
  = coe
      d_is'45'finite'45'type'45'UU'45'Fin'45'Level_298 (coe ()) (coe v0)
      (coe v1)
-- univalent-combinatorics.finite-types.all-elements-equal-has-finite-cardinality
d_all'45'elements'45'equal'45'has'45'finite'45'cardinality_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_all'45'elements'45'equal'45'has'45'finite'45'cardinality_314
  = erased
-- univalent-combinatorics.finite-types.is-prop-has-finite-cardinality
d_is'45'prop'45'has'45'finite'45'cardinality_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'has'45'finite'45'cardinality_338 ~v0 ~v1
  = du_is'45'prop'45'has'45'finite'45'cardinality_338
du_is'45'prop'45'has'45'finite'45'cardinality_338 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'has'45'finite'45'cardinality_338 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'all'45'elements'45'equal_70
-- univalent-combinatorics.finite-types.has-finite-cardinality-Prop
d_has'45'finite'45'cardinality'45'Prop_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_has'45'finite'45'cardinality'45'Prop_344 ~v0 ~v1
  = du_has'45'finite'45'cardinality'45'Prop_344
du_has'45'finite'45'cardinality'45'Prop_344 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_has'45'finite'45'cardinality'45'Prop_344
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'has'45'finite'45'cardinality_338)
-- univalent-combinatorics.finite-types._.is-finite-has-finite-cardinality
d_is'45'finite'45'has'45'finite'45'cardinality_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'finite'45'has'45'finite'45'cardinality_358 v0 ~v1 v2
  = du_is'45'finite'45'has'45'finite'45'cardinality_358 v0 v2
du_is'45'finite'45'has'45'finite'45'cardinality_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_is'45'finite'45'has'45'finite'45'cardinality_358 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> coe
             MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
             (coe v0) (coe v0) (coe v3) (coe du_is'45'finite'45'Prop_6 (coe v0))
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                (coe (\ v4 -> coe du_is'45'finite'45'count_28 (coe v0)))
                (coe
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                   (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.finite-types._.is-finite-has-cardinality
d_is'45'finite'45'has'45'cardinality_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> Integer -> AgdaAny -> AgdaAny
d_is'45'finite'45'has'45'cardinality_366 v0 ~v1 v2 v3
  = du_is'45'finite'45'has'45'cardinality_366 v0 v2 v3
du_is'45'finite'45'has'45'cardinality_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer -> AgdaAny -> AgdaAny
du_is'45'finite'45'has'45'cardinality_366 v0 v1 v2
  = coe
      du_is'45'finite'45'has'45'finite'45'cardinality_358 (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v1) (coe v2))
-- univalent-combinatorics.finite-types._.has-finite-cardinality-count
d_has'45'finite'45'cardinality'45'count_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_has'45'finite'45'cardinality'45'count_372 v0 ~v1 v2
  = du_has'45'finite'45'cardinality'45'count_372 v0 v2
du_has'45'finite'45'cardinality'45'count_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_has'45'finite'45'cardinality'45'count_372 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_number'45'of'45'elements'45'count_22
         (coe v1))
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
         v0
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_equiv'45'count_24
            (coe v1)))
-- univalent-combinatorics.finite-types._.has-finite-cardinality-is-finite
d_has'45'finite'45'cardinality'45'is'45'finite_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_has'45'finite'45'cardinality'45'is'45'finite_378 v0 ~v1
  = du_has'45'finite'45'cardinality'45'is'45'finite_378 v0
du_has'45'finite'45'cardinality'45'is'45'finite_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_has'45'finite'45'cardinality'45'is'45'finite_378 v0
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_map'45'universal'45'property'45'trunc'45'Prop_176
      (coe v0) (coe v0) (coe du_has'45'finite'45'cardinality'45'Prop_344)
      (coe du_has'45'finite'45'cardinality'45'count_372 (coe v0))
-- univalent-combinatorics.finite-types._.number-of-elements-is-finite
d_number'45'of'45'elements'45'is'45'finite_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> Integer
d_number'45'of'45'elements'45'is'45'finite_380 v0 ~v1
  = du_number'45'of'45'elements'45'is'45'finite_380 v0
du_number'45'of'45'elements'45'is'45'finite_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny -> Integer
du_number'45'of'45'elements'45'is'45'finite_380 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
      (coe
         (\ v1 ->
            coe
              du_number'45'of'45'elements'45'has'45'finite'45'cardinality_114))
      (coe du_has'45'finite'45'cardinality'45'is'45'finite_378 (coe v0))
-- univalent-combinatorics.finite-types._.mere-equiv-is-finite
d_mere'45'equiv'45'is'45'finite_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> AgdaAny
d_mere'45'equiv'45'is'45'finite_384 v0 ~v1 v2
  = du_mere'45'equiv'45'is'45'finite_384 v0 v2
du_mere'45'equiv'45'is'45'finite_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny -> AgdaAny
du_mere'45'equiv'45'is'45'finite_384 v0 v1
  = coe
      du_mere'45'equiv'45'has'45'finite'45'cardinality_122
      (coe du_has'45'finite'45'cardinality'45'is'45'finite_378 v0 v1)
-- univalent-combinatorics.finite-types._.compute-number-of-elements-is-finite
d_compute'45'number'45'of'45'elements'45'is'45'finite_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_compute'45'number'45'of'45'elements'45'is'45'finite_392 = erased
-- univalent-combinatorics.finite-types.eq-cardinality
d_eq'45'cardinality_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  Integer ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'cardinality_410 = erased
-- univalent-combinatorics.finite-types.is-empty-is-zero-number-of-elements-is-finite
d_is'45'empty'45'is'45'zero'45'number'45'of'45'elements'45'is'45'finite_426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'is'45'zero'45'number'45'of'45'elements'45'is'45'finite_426
  = erased
-- univalent-combinatorics.finite-types.map-compute-total-UU-Fin
d_map'45'compute'45'total'45'UU'45'Fin_438 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'compute'45'total'45'UU'45'Fin_438 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> case coe v2 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                  -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> case coe v2 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                  -> coe
                       du_is'45'finite'45'has'45'finite'45'cardinality_358
                       (coe MAlonzo.Code.Agda.Primitive.d_lzero_16)
                       (coe
                          MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                          (coe v1) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- univalent-combinatorics.finite-types.compute-total-UU-Fin
d_compute'45'total'45'UU'45'Fin_452 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_compute'45'total'45'UU'45'Fin_452
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v0 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_equiv'45'prop_154
                 (coe du_is'45'finite'45'has'45'finite'45'cardinality_358 (coe ()))
                 (coe
                    du_has'45'finite'45'cardinality'45'is'45'finite_378 (coe ())))))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'left'45'swap'45'Σ_464)
-- univalent-combinatorics.finite-types.is-inhabited-or-empty-is-finite
d_is'45'inhabited'45'or'45'empty'45'is'45'finite_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'inhabited'45'or'45'empty'45'is'45'finite_460 v0 ~v1 v2
  = du_is'45'inhabited'45'or'45'empty'45'is'45'finite_460 v0 v2
du_is'45'inhabited'45'or'45'empty'45'is'45'finite_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'inhabited'45'or'45'empty'45'is'45'finite_460 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe v0) (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'inhabited'45'or'45'empty'45'Prop_390)
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_is'45'inhabited'45'or'45'empty'45'count_206
         (coe v0))
-- univalent-combinatorics.finite-types.is-decidable-type-trunc-Prop-is-finite
d_is'45'decidable'45'type'45'trunc'45'Prop'45'is'45'finite_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'type'45'trunc'45'Prop'45'is'45'finite_472 v0
                                                               ~v1 v2
  = du_is'45'decidable'45'type'45'trunc'45'Prop'45'is'45'finite_472
      v0 v2
du_is'45'decidable'45'type'45'trunc'45'Prop'45'is'45'finite_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'decidable'45'type'45'trunc'45'Prop'45'is'45'finite_472 v0
                                                                v1
  = coe
      MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_map'45'coprod_24
      (coe (\ v2 -> v2))
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_map'45'universal'45'property'45'trunc'45'Prop_176
         (coe v0) (coe ())
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.d_empty'45'Prop_90))
      (coe
         du_is'45'inhabited'45'or'45'empty'45'is'45'finite_460 (coe v0)
         (coe v1))
-- univalent-combinatorics.finite-types.is-finite-type-trunc-Prop
d_is'45'finite'45'type'45'trunc'45'Prop_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> AgdaAny
d_is'45'finite'45'type'45'trunc'45'Prop_480 v0 ~v1
  = du_is'45'finite'45'type'45'trunc'45'Prop_480 v0
du_is'45'finite'45'type'45'trunc'45'Prop_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny -> AgdaAny
du_is'45'finite'45'type'45'trunc'45'Prop_480 v0
  = coe
      MAlonzo.Code.Qfoundation.QfunctorialityZ45ZpropositionalZ45Ztruncation.du_functor'45'trunc'45'Prop_36
      (coe v0) (coe v0)
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting.du_count'45'type'45'trunc'45'Prop_218
         (coe v0))
-- univalent-combinatorics.finite-types.trunc-Prop-𝔽
d_trunc'45'Prop'45'𝔽_482 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_trunc'45'Prop'45'𝔽_482 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'finite'45'type'45'trunc'45'Prop_480 ()
         (d_is'45'finite'45'type'45'𝔽_38 (coe v0)))
-- univalent-combinatorics.finite-types.equiv-UU-Fin-Level
d_equiv'45'UU'45'Fin'45'Level_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_equiv'45'UU'45'Fin'45'Level_494 = erased
-- univalent-combinatorics.finite-types.id-equiv-UU-Fin-Level
d_id'45'equiv'45'UU'45'Fin'45'Level_506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_id'45'equiv'45'UU'45'Fin'45'Level_506 ~v0 ~v1 ~v2
  = du_id'45'equiv'45'UU'45'Fin'45'Level_506
du_id'45'equiv'45'UU'45'Fin'45'Level_506 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_id'45'equiv'45'UU'45'Fin'45'Level_506
  = coe
      MAlonzo.Code.Qfoundation.QconnectedZ45ZcomponentsZ45Zuniverses.du_id'45'equiv'45'component'45'UU'45'Level_92
-- univalent-combinatorics.finite-types.equiv-eq-UU-Fin-Level
d_equiv'45'eq'45'UU'45'Fin'45'Level_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'eq'45'UU'45'Fin'45'Level_518 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_equiv'45'eq'45'UU'45'Fin'45'Level_518
du_equiv'45'eq'45'UU'45'Fin'45'Level_518 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'eq'45'UU'45'Fin'45'Level_518
  = coe
      MAlonzo.Code.Qfoundation.QconnectedZ45ZcomponentsZ45Zuniverses.du_equiv'45'eq'45'component'45'UU'45'Level_106
-- univalent-combinatorics.finite-types.is-contr-total-equiv-UU-Fin-Level
d_is'45'contr'45'total'45'equiv'45'UU'45'Fin'45'Level_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'equiv'45'UU'45'Fin'45'Level_528 ~v0 ~v1
                                                          v2
  = du_is'45'contr'45'total'45'equiv'45'UU'45'Fin'45'Level_528 v2
du_is'45'contr'45'total'45'equiv'45'UU'45'Fin'45'Level_528 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'equiv'45'UU'45'Fin'45'Level_528 v0
  = coe
      MAlonzo.Code.Qfoundation.QconnectedZ45ZcomponentsZ45Zuniverses.du_is'45'contr'45'total'45'equiv'45'component'45'UU'45'Level_118
      (coe v0)
-- univalent-combinatorics.finite-types.is-equiv-equiv-eq-UU-Fin-Level
d_is'45'equiv'45'equiv'45'eq'45'UU'45'Fin'45'Level_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'equiv'45'eq'45'UU'45'Fin'45'Level_544 ~v0 ~v1 v2
  = du_is'45'equiv'45'equiv'45'eq'45'UU'45'Fin'45'Level_544 v2
du_is'45'equiv'45'equiv'45'eq'45'UU'45'Fin'45'Level_544 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'equiv'45'eq'45'UU'45'Fin'45'Level_544 v0
  = coe
      MAlonzo.Code.Qfoundation.QconnectedZ45ZcomponentsZ45Zuniverses.du_is'45'equiv'45'equiv'45'eq'45'component'45'UU'45'Level_134
      (coe v0)
-- univalent-combinatorics.finite-types.eq-equiv-UU-Fin-Level
d_eq'45'equiv'45'UU'45'Fin'45'Level_556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'equiv'45'UU'45'Fin'45'Level_556 = erased
-- univalent-combinatorics.finite-types.equiv-equiv-eq-UU-Fin-Level
d_equiv'45'equiv'45'eq'45'UU'45'Fin'45'Level_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'equiv'45'eq'45'UU'45'Fin'45'Level_570 ~v0 ~v1 v2 v3
  = du_equiv'45'equiv'45'eq'45'UU'45'Fin'45'Level_570 v2 v3
du_equiv'45'equiv'45'eq'45'UU'45'Fin'45'Level_570 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'equiv'45'eq'45'UU'45'Fin'45'Level_570 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (\ v2 -> coe du_equiv'45'eq'45'UU'45'Fin'45'Level_518)
      (coe du_is'45'equiv'45'equiv'45'eq'45'UU'45'Fin'45'Level_544 v0 v1)
-- univalent-combinatorics.finite-types.equiv-UU-Fin
d_equiv'45'UU'45'Fin_586 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_equiv'45'UU'45'Fin_586 = erased
-- univalent-combinatorics.finite-types.id-equiv-UU-Fin
d_id'45'equiv'45'UU'45'Fin_596 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_id'45'equiv'45'UU'45'Fin_596 ~v0 ~v1
  = du_id'45'equiv'45'UU'45'Fin_596
du_id'45'equiv'45'UU'45'Fin_596 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_id'45'equiv'45'UU'45'Fin_596
  = coe
      MAlonzo.Code.Qfoundation.QconnectedZ45ZcomponentsZ45Zuniverses.du_id'45'equiv'45'component'45'UU_176
-- univalent-combinatorics.finite-types.equiv-eq-UU-Fin
d_equiv'45'eq'45'UU'45'Fin_606 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'eq'45'UU'45'Fin_606 ~v0 ~v1 ~v2 ~v3
  = du_equiv'45'eq'45'UU'45'Fin_606
du_equiv'45'eq'45'UU'45'Fin_606 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'eq'45'UU'45'Fin_606
  = coe
      MAlonzo.Code.Qfoundation.QconnectedZ45ZcomponentsZ45Zuniverses.du_equiv'45'eq'45'component'45'UU_188
-- univalent-combinatorics.finite-types.is-contr-total-equiv-UU-Fin
d_is'45'contr'45'total'45'equiv'45'UU'45'Fin_614 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'equiv'45'UU'45'Fin_614 ~v0 v1
  = du_is'45'contr'45'total'45'equiv'45'UU'45'Fin_614 v1
du_is'45'contr'45'total'45'equiv'45'UU'45'Fin_614 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'equiv'45'UU'45'Fin_614 v0
  = coe
      MAlonzo.Code.Qfoundation.QconnectedZ45ZcomponentsZ45Zuniverses.du_is'45'contr'45'total'45'equiv'45'component'45'UU_198
      (coe v0)
-- univalent-combinatorics.finite-types.is-equiv-equiv-eq-UU-Fin
d_is'45'equiv'45'equiv'45'eq'45'UU'45'Fin_624 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'equiv'45'eq'45'UU'45'Fin_624 ~v0 v1
  = du_is'45'equiv'45'equiv'45'eq'45'UU'45'Fin_624 v1
du_is'45'equiv'45'equiv'45'eq'45'UU'45'Fin_624 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'equiv'45'eq'45'UU'45'Fin_624 v0
  = coe
      MAlonzo.Code.Qfoundation.QconnectedZ45ZcomponentsZ45Zuniverses.du_is'45'equiv'45'equiv'45'eq'45'component'45'UU_210
      (coe v0)
-- univalent-combinatorics.finite-types.eq-equiv-UU-Fin
d_eq'45'equiv'45'UU'45'Fin_634 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'equiv'45'UU'45'Fin_634 = erased
-- univalent-combinatorics.finite-types.equiv-equiv-eq-UU-Fin
d_equiv'45'equiv'45'eq'45'UU'45'Fin_646 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'equiv'45'eq'45'UU'45'Fin_646 ~v0 v1 v2
  = du_equiv'45'equiv'45'eq'45'UU'45'Fin_646 v1 v2
du_equiv'45'equiv'45'eq'45'UU'45'Fin_646 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'equiv'45'eq'45'UU'45'Fin_646 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (\ v2 -> coe du_equiv'45'eq'45'UU'45'Fin_606)
      (coe du_is'45'equiv'45'equiv'45'eq'45'UU'45'Fin_624 v0 v1)
-- univalent-combinatorics.finite-types.is-path-connected-UU-Fin-Level
d_is'45'path'45'connected'45'UU'45'Fin'45'Level_660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'path'45'connected'45'UU'45'Fin'45'Level_660 v0 ~v1
  = du_is'45'path'45'connected'45'UU'45'Fin'45'Level_660 v0
du_is'45'path'45'connected'45'UU'45'Fin'45'Level_660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'path'45'connected'45'UU'45'Fin'45'Level_660 v0
  = coe
      MAlonzo.Code.Qfoundation.QconnectedZ45Ztypes.du_is'45'path'45'connected'45'mere'45'eq_54
      (coe ()) (coe du_Fin'45'UU'45'Fin'45'Level_260 (coe v0))
-- univalent-combinatorics.finite-types.is-path-connected-UU-Fin
d_is'45'path'45'connected'45'UU'45'Fin_670 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'path'45'connected'45'UU'45'Fin_670 ~v0
  = du_is'45'path'45'connected'45'UU'45'Fin_670
du_is'45'path'45'connected'45'UU'45'Fin_670 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'path'45'connected'45'UU'45'Fin_670
  = coe
      MAlonzo.Code.Qfoundation.QconnectedZ45Ztypes.du_is'45'path'45'connected'45'mere'45'eq_54
      (coe ()) (coe du_Fin'45'UU'45'Fin_250)
