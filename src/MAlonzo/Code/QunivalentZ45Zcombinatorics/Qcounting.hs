{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QunivalentZ45Zcombinatorics.Qcounting where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qsets
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Zequality
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes

-- univalent-combinatorics.counting.count
d_count_6 :: MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_count_6 = erased
-- univalent-combinatorics.counting._.number-of-elements-count
d_number'45'of'45'elements'45'count_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  Integer
d_number'45'of'45'elements'45'count_22 ~v0 ~v1 v2
  = du_number'45'of'45'elements'45'count_22 v2
du_number'45'of'45'elements'45'count_22 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  Integer
du_number'45'of'45'elements'45'count_22 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe v0)
-- univalent-combinatorics.counting._.equiv-count
d_equiv'45'count_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'count_24 ~v0 ~v1 v2 = du_equiv'45'count_24 v2
du_equiv'45'count_24 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'count_24 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe v0)
-- univalent-combinatorics.counting._.map-equiv-count
d_map'45'equiv'45'count_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_map'45'equiv'45'count_26 ~v0 ~v1 v2
  = du_map'45'equiv'45'count_26 v2
du_map'45'equiv'45'count_26 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_map'45'equiv'45'count_26 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe du_equiv'45'count_24 (coe v0))
-- univalent-combinatorics.counting._.map-inv-equiv-count
d_map'45'inv'45'equiv'45'count_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_map'45'inv'45'equiv'45'count_28 ~v0 ~v1 v2
  = du_map'45'inv'45'equiv'45'count_28 v2
du_map'45'inv'45'equiv'45'count_28 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_map'45'inv'45'equiv'45'count_28 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'equiv_240
      (coe du_equiv'45'count_24 (coe v0))
-- univalent-combinatorics.counting._.inv-equiv-count
d_inv'45'equiv'45'count_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'equiv'45'count_30 ~v0 ~v1 v2
  = du_inv'45'equiv'45'count_30 v2
du_inv'45'equiv'45'count_30 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'equiv'45'count_30 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
      (coe du_equiv'45'count_24 (coe v0))
-- univalent-combinatorics.counting._.is-set-count
d_is'45'set'45'count_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'count_32 ~v0 ~v1 v2 = du_is'45'set'45'count_32 v2
du_is'45'set'45'count_32 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'count_32 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qsets.du_is'45'set'45'equiv''_210
      erased erased (coe du_equiv'45'count_24 (coe v0))
      (MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes.d_is'45'set'45'Fin_152
         (coe du_number'45'of'45'elements'45'count_22 (coe v0)))
-- univalent-combinatorics.counting.count-Fin
d_count'45'Fin_36 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'Fin_36 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92)
-- univalent-combinatorics.counting._.equiv-count-equiv
d_equiv'45'count'45'equiv_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'count'45'equiv_58 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_equiv'45'count'45'equiv_58 v4 v5
du_equiv'45'count'45'equiv_58 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'count'45'equiv_58 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386 v0
      (coe du_equiv'45'count_24 (coe v1))
-- univalent-combinatorics.counting._.count-equiv
d_count'45'equiv_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'equiv_64 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_count'45'equiv_64 v4 v5
du_count'45'equiv_64 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'equiv_64 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_number'45'of'45'elements'45'count_22 (coe v1))
      (coe du_equiv'45'count'45'equiv_58 (coe v0) (coe v1))
-- univalent-combinatorics.counting._.equiv-count-equiv'
d_equiv'45'count'45'equiv''_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'count'45'equiv''_78 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_equiv'45'count'45'equiv''_78 v4 v5
du_equiv'45'count'45'equiv''_78 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'count'45'equiv''_78 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
         (coe v0))
      (coe du_equiv'45'count_24 (coe v1))
-- univalent-combinatorics.counting._.count-equiv'
d_count'45'equiv''_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'equiv''_84 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_count'45'equiv''_84 v4 v5
du_count'45'equiv''_84 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'equiv''_84 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_number'45'of'45'elements'45'count_22 (coe v1))
      (coe du_equiv'45'count'45'equiv''_78 (coe v0) (coe v1))
-- univalent-combinatorics.counting._.count-is-equiv
d_count'45'is'45'equiv_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'is'45'equiv_96 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_count'45'is'45'equiv_96 v4 v5
du_count'45'is'45'equiv_96 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'is'45'equiv_96 v0 v1
  = coe
      du_count'45'equiv_64
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v0) (coe v1))
-- univalent-combinatorics.counting._.count-is-equiv'
d_count'45'is'45'equiv''_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'is'45'equiv''_102 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_count'45'is'45'equiv''_102 v4 v5
du_count'45'is'45'equiv''_102 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'is'45'equiv''_102 v0 v1
  = coe
      du_count'45'equiv''_84
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v0) (coe v1))
-- univalent-combinatorics.counting.is-empty-is-zero-number-of-elements-count
d_is'45'empty'45'is'45'zero'45'number'45'of'45'elements'45'count_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'is'45'zero'45'number'45'of'45'elements'45'count_112
  = erased
-- univalent-combinatorics.counting.is-zero-number-of-elements-count-is-empty
d_is'45'zero'45'number'45'of'45'elements'45'count'45'is'45'empty_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'number'45'of'45'elements'45'count'45'is'45'empty_124
  = erased
-- univalent-combinatorics.counting.count-is-empty
d_count'45'is'45'empty_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'is'45'empty_140 ~v0 ~v1 v2
  = du_count'45'is'45'empty_140 v2
du_count'45'is'45'empty_140 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'is'45'empty_140 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
            (coe v0)
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'equiv'45'is'45'empty''_70)))
-- univalent-combinatorics.counting.count-empty
d_count'45'empty_146 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'empty_146 = coe d_count'45'Fin_36 (coe (0 :: Integer))
-- univalent-combinatorics.counting.count-is-contr
d_count'45'is'45'contr_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'is'45'contr_152 ~v0 ~v1 v2
  = du_count'45'is'45'contr_152 v2
du_count'45'is'45'contr_152 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'is'45'contr_152 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (1 :: Integer))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_equiv'45'is'45'contr_250
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_is'45'contr'45'Fin'45'one'45'ℕ_122)
         (coe v0))
-- univalent-combinatorics.counting.is-contr-is-one-number-of-elements-count
d_is'45'contr'45'is'45'one'45'number'45'of'45'elements'45'count_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'is'45'one'45'number'45'of'45'elements'45'count_164 ~v0
                                                                    ~v1 v2 ~v3
  = du_is'45'contr'45'is'45'one'45'number'45'of'45'elements'45'count_164
      v2
du_is'45'contr'45'is'45'one'45'number'45'of'45'elements'45'count_164 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'is'45'one'45'number'45'of'45'elements'45'count_164 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
             (coe v2)
             (coe
                MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_is'45'contr'45'Fin'45'one'45'ℕ_122)
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.counting.is-one-number-of-elements-count-is-contr
d_is'45'one'45'number'45'of'45'elements'45'count'45'is'45'contr_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'number'45'of'45'elements'45'count'45'is'45'contr_174
  = erased
-- univalent-combinatorics.counting.count-unit
d_count'45'unit_190 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'unit_190
  = coe
      du_count'45'is'45'contr_152
      (coe
         MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_is'45'contr'45'unit_42)
-- univalent-combinatorics.counting.has-decidable-equality-count
d_has'45'decidable'45'equality'45'count_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'count_196 ~v0 ~v1 v2
  = du_has'45'decidable'45'equality'45'count_196 v2
du_has'45'decidable'45'equality'45'count_196 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_has'45'decidable'45'equality'45'count_196 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> coe
             MAlonzo.Code.Qfoundation.QdecidableZ45Zequality.du_has'45'decidable'45'equality'45'equiv''_284
             v2
             (coe
                MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes.du_has'45'decidable'45'equality'45'Fin_112)
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.counting.is-inhabited-or-empty-count
d_is'45'inhabited'45'or'45'empty'45'count_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'inhabited'45'or'45'empty'45'count_206 v0 ~v1 v2
  = du_is'45'inhabited'45'or'45'empty'45'count_206 v0 v2
du_is'45'inhabited'45'or'45'empty'45'count_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_is'45'inhabited'45'or'45'empty'45'count_206 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> case coe v2 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
             _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                    (coe
                       MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
                       v0
                       (coe
                          MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                          v3
                          (MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_zero'45'Fin_230
                             (coe v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- univalent-combinatorics.counting.count-type-trunc-Prop
d_count'45'type'45'trunc'45'Prop_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_count'45'type'45'trunc'45'Prop_218 v0 ~v1 v2
  = du_count'45'type'45'trunc'45'Prop_218 v0 v2
du_count'45'type'45'trunc'45'Prop_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_count'45'type'45'trunc'45'Prop_218 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> case coe v2 of
             0 -> coe du_count'45'is'45'empty_140 erased
             _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    du_count'45'is'45'contr_152
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
                       (coe
                          MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_is'45'prop'45'type'45'trunc'45'Prop_18
                          (coe v0))
                       (coe
                          MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
                          v0
                          (coe
                             MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                             v3
                             (MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_zero'45'Fin_230
                                (coe v4)))))
      _ -> MAlonzo.RTE.mazUnreachableError
