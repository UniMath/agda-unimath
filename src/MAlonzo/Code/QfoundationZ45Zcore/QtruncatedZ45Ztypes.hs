{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qembeddings
import qualified MAlonzo.Code.QfoundationZ45Zcore.QequalityZ45ZcartesianZ45ZproductZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QequalityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qretractions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels

-- foundation-core.truncated-types.is-trunc
d_is'45'trunc_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () -> ()
d_is'45'trunc_8 = erased
-- foundation-core.truncated-types.Truncated-Type
d_Truncated'45'Type_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 -> ()
d_Truncated'45'Type_22 = erased
-- foundation-core.truncated-types._.type-Truncated-Type
d_type'45'Truncated'45'Type_36 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'Truncated'45'Type_36 = erased
-- foundation-core.truncated-types._.is-trunc-type-Truncated-Type
d_is'45'trunc'45'type'45'Truncated'45'Type_40 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'trunc'45'type'45'Truncated'45'Type_40 ~v0 ~v1
  = du_is'45'trunc'45'type'45'Truncated'45'Type_40
du_is'45'trunc'45'type'45'Truncated'45'Type_40 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_is'45'trunc'45'type'45'Truncated'45'Type_40
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
-- foundation-core.truncated-types.is-trunc-succ-is-trunc
d_is'45'trunc'45'succ'45'is'45'trunc_48 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'succ'45'is'45'trunc_48 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6
        -> coe
             (\ v1 v2 v3 v4 v5 ->
                coe
                  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                  erased erased)
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8 v1
        -> coe
             (\ v2 v3 v4 v5 v6 ->
                coe
                  d_is'45'trunc'45'succ'45'is'45'trunc_48 v1 v2 erased
                  (coe v4 v5 v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.truncated-types.truncated-type-succ-Truncated-Type
d_truncated'45'type'45'succ'45'Truncated'45'Type_72 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_truncated'45'type'45'succ'45'Truncated'45'Type_72 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         d_is'45'trunc'45'succ'45'is'45'trunc_48 v0 v1 erased
         (coe du_is'45'trunc'45'type'45'Truncated'45'Type_40 v2))
-- foundation-core.truncated-types.is-trunc-Id
d_is'45'trunc'45'Id_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'Id_92 v0 v1 ~v2 = du_is'45'trunc'45'Id_92 v0 v1
du_is'45'trunc'45'Id_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'Id_92 v0 v1
  = coe d_is'45'trunc'45'succ'45'is'45'trunc_48 v1 v0 erased
-- foundation-core.truncated-types.Id-Truncated-Type
d_Id'45'Truncated'45'Type_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Id'45'Truncated'45'Type_108 ~v0 ~v1 v2 v3 v4
  = du_Id'45'Truncated'45'Type_108 v2 v3 v4
du_Id'45'Truncated'45'Type_108 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Id'45'Truncated'45'Type_108 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe du_is'45'trunc'45'type'45'Truncated'45'Type_40 v0 v1 v2)
-- foundation-core.truncated-types.Id-Truncated-Type'
d_Id'45'Truncated'45'Type''_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Id'45'Truncated'45'Type''_132 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'trunc'45'Id_92 v0 v1
         (coe du_is'45'trunc'45'type'45'Truncated'45'Type_40 v2) v3 v4)
-- foundation-core.truncated-types._.is-trunc-retract-of
d_is'45'trunc'45'retract'45'of_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_is'45'trunc'45'retract'45'of_160 ~v0 ~v1 v2 ~v3 ~v4
  = du_is'45'trunc'45'retract'45'of_160 v2
du_is'45'trunc'45'retract'45'of_160 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_is'45'trunc'45'retract'45'of_160 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'retract'45'of_128
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8 v1
        -> coe
             (\ v2 v3 v4 v5 ->
                coe
                  du_is'45'trunc'45'retract'45'of_160 v1
                  (coe
                     MAlonzo.Code.QfoundationZ45Zcore.Qretractions.du_retract'45'eq_172
                     (coe v2))
                  (coe
                     v3
                     (coe
                        MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                        v2 v4)
                     (coe
                        MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                        v2 v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.truncated-types.is-trunc-is-equiv
d_is'45'trunc'45'is'45'equiv_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_is'45'trunc'45'is'45'equiv_184 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_is'45'trunc'45'is'45'equiv_184 v2 v5 v6
du_is'45'trunc'45'is'45'equiv_184 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_is'45'trunc'45'is'45'equiv_184 v0 v1 v2
  = coe
      du_is'45'trunc'45'retract'45'of_160 v0
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v1)
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
            (coe v2)))
-- foundation-core.truncated-types.is-trunc-equiv
d_is'45'trunc'45'equiv_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_is'45'trunc'45'equiv_206 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_is'45'trunc'45'equiv_206 v2 v5
du_is'45'trunc'45'equiv_206 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_is'45'trunc'45'equiv_206 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> coe du_is'45'trunc'45'is'45'equiv_184 (coe v0) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.truncated-types.is-trunc-is-equiv'
d_is'45'trunc'45'is'45'equiv''_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_is'45'trunc'45'is'45'equiv''_228 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_is'45'trunc'45'is'45'equiv''_228 v2 v5 v6 v7
du_is'45'trunc'45'is'45'equiv''_228 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_is'45'trunc'45'is'45'equiv''_228 v0 v1 v2 v3
  = coe
      du_is'45'trunc'45'is'45'equiv_184 v0
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'is'45'equiv_216
         (coe v2))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'inv'45'is'45'equiv_224
         (coe v1))
      v3
-- foundation-core.truncated-types.is-trunc-equiv'
d_is'45'trunc'45'equiv''_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_is'45'trunc'45'equiv''_252 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_is'45'trunc'45'equiv''_252 v2 v5
du_is'45'trunc'45'equiv''_252 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_is'45'trunc'45'equiv''_252 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> coe
             du_is'45'trunc'45'is'45'equiv''_228 (coe v0) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.truncated-types.is-trunc-is-emb
d_is'45'trunc'45'is'45'emb_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'is'45'emb_274 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_is'45'trunc'45'is'45'emb_274 v2 v5 v6 v7 v8 v9
du_is'45'trunc'45'is'45'emb_274 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'is'45'emb_274 v0 v1 v2 v3 v4 v5
  = coe
      du_is'45'trunc'45'is'45'equiv_184 v0 erased (coe v2 v4 v5)
      (coe v3 (coe v1 v4) (coe v1 v5))
-- foundation-core.truncated-types.is-trunc-emb
d_is'45'trunc'45'emb_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'emb_300 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_is'45'trunc'45'emb_300 v2 v5
du_is'45'trunc'45'emb_300 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'emb_300 v0 v1
  = coe
      du_is'45'trunc'45'is'45'emb_274 (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qembeddings.du_map'45'emb_46
         (coe v1))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qembeddings.du_is'45'emb'45'map'45'emb_52
         (coe v1))
-- foundation-core.truncated-types.is-trunc-Σ
d_is'45'trunc'45'Σ_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_is'45'trunc'45'Σ_318 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_is'45'trunc'45'Σ_318 v2 v5 v6
du_is'45'trunc'45'Σ_318 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_is'45'trunc'45'Σ_318 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'Σ''_356
             (coe v1) (coe v2)
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8 v3
        -> coe
             (\ v4 v5 ->
                coe
                  du_is'45'trunc'45'equiv_206 v3
                  (coe
                     MAlonzo.Code.QfoundationZ45Zcore.QequalityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'pair'45'eq'45'Σ_124)
                  (coe
                     du_is'45'trunc'45'Σ_318 (coe v3)
                     (coe
                        v1
                        (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                           (coe v4))
                        (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                           (coe v5)))
                     (coe
                        (\ v6 ->
                           coe
                             v2
                             (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                                (coe v5))
                             (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
                                (coe v4))
                             (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
                                (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.truncated-types.Σ-Truncated-Type
d_Σ'45'Truncated'45'Type_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Σ'45'Truncated'45'Type_350 ~v0 ~v1 v2 v3 v4
  = du_Σ'45'Truncated'45'Type_350 v2 v3 v4
du_Σ'45'Truncated'45'Type_350 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Σ'45'Truncated'45'Type_350 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'trunc'45'Σ_318 (coe v0)
         (coe du_is'45'trunc'45'type'45'Truncated'45'Type_40 v1)
         (coe
            (\ v3 ->
               coe du_is'45'trunc'45'type'45'Truncated'45'Type_40 (coe v2 v3))))
-- foundation-core.truncated-types.fib-Truncated-Type
d_fib'45'Truncated'45'Type_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_fib'45'Truncated'45'Type_376 ~v0 v1 v2 v3 v4 v5 v6
  = du_fib'45'Truncated'45'Type_376 v1 v2 v3 v4 v5 v6
du_fib'45'Truncated'45'Type_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_fib'45'Truncated'45'Type_376 v0 v1 v2 v3 v4 v5
  = coe
      du_Σ'45'Truncated'45'Type_350 (coe v1) (coe v2)
      (coe
         (\ v6 ->
            d_Id'45'Truncated'45'Type''_132
              (coe v0) (coe v1) (coe v3) (coe v4 v6) (coe v5)))
-- foundation-core.truncated-types.is-trunc-prod
d_is'45'trunc'45'prod_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'prod_398 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_is'45'trunc'45'prod_398 v2 v5 v6
du_is'45'trunc'45'prod_398 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'prod_398 v0 v1 v2
  = coe du_is'45'trunc'45'Σ_318 (coe v0) (coe v1) (coe (\ v3 -> v2))
-- foundation-core.truncated-types.is-trunc-prod'
d_is'45'trunc'45'prod''_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'trunc'45'prod''_418 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8
  = du_is'45'trunc'45'prod''_418 v2 v5 v6 v7 v8
du_is'45'trunc'45'prod''_418 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_is'45'trunc'45'prod''_418 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v5 v6
        -> case coe v4 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v7 v8
               -> coe
                    du_is'45'trunc'45'equiv_206 v0
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QequalityZ45ZcartesianZ45ZproductZ45Ztypes.du_equiv'45'pair'45'eq_126)
                    (coe
                       du_is'45'trunc'45'prod_398 (coe v0) (coe v1 v6 v5 v7)
                       (coe v2 v5 v6 v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.truncated-types.is-trunc-left-factor-prod
d_is'45'trunc'45'left'45'factor'45'prod_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'left'45'factor'45'prod_444 ~v0 ~v1 v2 ~v3 ~v4 v5
                                            v6
  = du_is'45'trunc'45'left'45'factor'45'prod_444 v2 v5 v6
du_is'45'trunc'45'left'45'factor'45'prod_444 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'left'45'factor'45'prod_444 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'left'45'factor'45'prod_274
             (coe v1)
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8 v3
        -> coe
             (\ v4 v5 ->
                coe
                  du_is'45'trunc'45'left'45'factor'45'prod_444 (coe v3)
                  (coe
                     du_is'45'trunc'45'equiv''_252 v3
                     (coe
                        MAlonzo.Code.QfoundationZ45Zcore.QequalityZ45ZcartesianZ45ZproductZ45Ztypes.du_equiv'45'pair'45'eq_126)
                     (coe
                        v1
                        (coe
                           MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                           (coe v4) (coe v2))
                        (coe
                           MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                           (coe v5) (coe v2))))
                  erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.truncated-types.is-trunc-right-factor-prod
d_is'45'trunc'45'right'45'factor'45'prod_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'right'45'factor'45'prod_474 ~v0 ~v1 v2 ~v3 ~v4 v5
                                             v6
  = du_is'45'trunc'45'right'45'factor'45'prod_474 v2 v5 v6
du_is'45'trunc'45'right'45'factor'45'prod_474 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'right'45'factor'45'prod_474 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'right'45'factor'45'prod_294
             (coe v1)
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8 v3
        -> coe
             (\ v4 v5 ->
                coe
                  du_is'45'trunc'45'right'45'factor'45'prod_474 (coe v3)
                  (coe
                     du_is'45'trunc'45'equiv''_252 v3
                     (coe
                        MAlonzo.Code.QfoundationZ45Zcore.QequalityZ45ZcartesianZ45ZproductZ45Ztypes.du_equiv'45'pair'45'eq_126)
                     (coe
                        v1
                        (coe
                           MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                           (coe v2) (coe v4))
                        (coe
                           MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                           (coe v2) (coe v5))))
                  erased)
      _ -> MAlonzo.RTE.mazUnreachableError
