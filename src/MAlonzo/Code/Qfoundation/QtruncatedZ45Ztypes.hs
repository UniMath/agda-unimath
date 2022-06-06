{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qequivalences
import qualified MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality

-- foundation.truncated-types.is-trunc-Π
d_is'45'trunc'45'Π_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> AgdaAny
d_is'45'trunc'45'Π_18 v0 v1 v2 ~v3 ~v4 v5
  = du_is'45'trunc'45'Π_18 v0 v1 v2 v5
du_is'45'trunc'45'Π_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny) -> AgdaAny
du_is'45'trunc'45'Π_18 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6
        -> coe
             MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes.du_is'45'contr'45'Π_16
             (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8 v4
        -> coe
             (\ v5 v6 ->
                coe
                  MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'is'45'equiv_184
                  v4 erased
                  (coe
                     MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality.d_funext_52 v0
                     v1 erased erased v5 v6)
                  (coe
                     du_is'45'trunc'45'Π_18 (coe v0) (coe v1) (coe v4)
                     (coe (\ v7 -> coe v3 v7 (coe v5 v7) (coe v6 v7)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.truncated-types.type-Π-Truncated-Type'
d_type'45'Π'45'Truncated'45'Type''_42 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  ()
d_type'45'Π'45'Truncated'45'Type''_42 = erased
-- foundation.truncated-types.is-trunc-type-Π-Truncated-Type'
d_is'45'trunc'45'type'45'Π'45'Truncated'45'Type''_62 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny
d_is'45'trunc'45'type'45'Π'45'Truncated'45'Type''_62 v0 v1 v2 ~v3
                                                     v4
  = du_is'45'trunc'45'type'45'Π'45'Truncated'45'Type''_62 v0 v1 v2 v4
du_is'45'trunc'45'type'45'Π'45'Truncated'45'Type''_62 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny
du_is'45'trunc'45'type'45'Π'45'Truncated'45'Type''_62 v0 v1 v2 v3
  = coe
      du_is'45'trunc'45'Π_18 (coe v1) (coe v2) (coe v0)
      (coe
         (\ v4 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'type'45'Truncated'45'Type_40
              (coe v3 v4)))
-- foundation.truncated-types.Π-Truncated-Type'
d_Π'45'Truncated'45'Type''_82 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Π'45'Truncated'45'Type''_82 v0 v1 v2 ~v3 v4
  = du_Π'45'Truncated'45'Type''_82 v0 v1 v2 v4
du_Π'45'Truncated'45'Type''_82 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Π'45'Truncated'45'Type''_82 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'trunc'45'type'45'Π'45'Truncated'45'Type''_62 (coe v0)
         (coe v1) (coe v2) (coe v3))
-- foundation.truncated-types.type-Π-Truncated-Type
d_type'45'Π'45'Truncated'45'Type_106 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  ()
d_type'45'Π'45'Truncated'45'Type_106 = erased
-- foundation.truncated-types.is-trunc-type-Π-Truncated-Type
d_is'45'trunc'45'type'45'Π'45'Truncated'45'Type_124 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny
d_is'45'trunc'45'type'45'Π'45'Truncated'45'Type_124 v0 v1 v2 ~v3 v4
  = du_is'45'trunc'45'type'45'Π'45'Truncated'45'Type_124 v0 v1 v2 v4
du_is'45'trunc'45'type'45'Π'45'Truncated'45'Type_124 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny
du_is'45'trunc'45'type'45'Π'45'Truncated'45'Type_124 v0 v1 v2 v3
  = coe
      du_is'45'trunc'45'type'45'Π'45'Truncated'45'Type''_62 (coe v0)
      (coe v1) (coe v2) (coe v3)
-- foundation.truncated-types.Π-Truncated-Type
d_Π'45'Truncated'45'Type_142 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Π'45'Truncated'45'Type_142 v0 v1 v2 ~v3 v4
  = du_Π'45'Truncated'45'Type_142 v0 v1 v2 v4
du_Π'45'Truncated'45'Type_142 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Π'45'Truncated'45'Type_142 v0 v1 v2 v3
  = coe
      du_Π'45'Truncated'45'Type''_82 (coe v0) (coe v1) (coe v2) (coe v3)
-- foundation.truncated-types.is-trunc-function-type
d_is'45'trunc'45'function'45'type_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () -> () -> AgdaAny -> AgdaAny
d_is'45'trunc'45'function'45'type_160 v0 v1 v2 ~v3 ~v4 v5
  = du_is'45'trunc'45'function'45'type_160 v0 v1 v2 v5
du_is'45'trunc'45'function'45'type_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> AgdaAny
du_is'45'trunc'45'function'45'type_160 v0 v1 v2 v3
  = coe
      du_is'45'trunc'45'Π_18 (coe v0) (coe v1) (coe v2)
      (coe (\ v4 -> v3))
-- foundation.truncated-types.type-hom-Truncated-Type
d_type'45'hom'45'Truncated'45'Type_184 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'hom'45'Truncated'45'Type_184 = erased
-- foundation.truncated-types.is-trunc-type-hom-Truncated-Type
d_is'45'trunc'45'type'45'hom'45'Truncated'45'Type_202 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'trunc'45'type'45'hom'45'Truncated'45'Type_202 v0 v1 v2 ~v3
                                                      v4
  = du_is'45'trunc'45'type'45'hom'45'Truncated'45'Type_202
      v0 v1 v2 v4
du_is'45'trunc'45'type'45'hom'45'Truncated'45'Type_202 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_is'45'trunc'45'type'45'hom'45'Truncated'45'Type_202 v0 v1 v2 v3
  = coe
      du_is'45'trunc'45'function'45'type_160 (coe v1) (coe v2) (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'type'45'Truncated'45'Type_40
         v3)
-- foundation.truncated-types.hom-Truncated-Type
d_hom'45'Truncated'45'Type_220 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_hom'45'Truncated'45'Type_220 v0 v1 v2 ~v3 v4
  = du_hom'45'Truncated'45'Type_220 v0 v1 v2 v4
du_hom'45'Truncated'45'Type_220 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_hom'45'Truncated'45'Type_220 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'trunc'45'type'45'hom'45'Truncated'45'Type_202 (coe v0)
         (coe v1) (coe v2) (coe v3))
-- foundation.truncated-types.is-prop-is-trunc
d_is'45'prop'45'is'45'trunc_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'trunc_240 v0 v1 ~v2
  = du_is'45'prop'45'is'45'trunc_240 v0 v1
du_is'45'prop'45'is'45'trunc_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'trunc_240 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6
        -> \ v2 ->
             coe
               MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes.du_is'45'subtype'45'is'45'contr_96
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8 v2
        -> coe
             du_is'45'trunc'45'Π_18 (coe v0) (coe v0)
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_neg'45'one'45'𝕋_10)
             (coe
                (\ v3 ->
                   coe
                     du_is'45'trunc'45'Π_18 (coe v0) (coe v0)
                     (coe
                        MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_neg'45'one'45'𝕋_10)
                     (coe
                        (\ v4 -> coe du_is'45'prop'45'is'45'trunc_240 (coe v0) (coe v2)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.truncated-types.is-trunc-Prop
d_is'45'trunc'45'Prop_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'trunc'45'Prop_258 v0 v1 ~v2
  = du_is'45'trunc'45'Prop_258 v0 v1
du_is'45'trunc'45'Prop_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'trunc'45'Prop_258 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'is'45'trunc_240 (coe v0) (coe v1))
-- foundation.truncated-types._.is-trunc-equiv-is-trunc
d_is'45'trunc'45'equiv'45'is'45'trunc_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'equiv'45'is'45'trunc_282 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_is'45'trunc'45'equiv'45'is'45'trunc_282 v0 v1 v4 v5 v6
du_is'45'trunc'45'equiv'45'is'45'trunc_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'equiv'45'is'45'trunc_282 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6
        -> coe
             MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv'45'is'45'contr_50
             (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8 v5
        -> coe
             (\ v6 v7 ->
                coe
                  MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'equiv_206
                  v5
                  (coe
                     MAlonzo.Code.Qfoundation.Qequivalences.du_extensionality'45'equiv_666
                     v6 v7)
                  (coe
                     du_is'45'trunc'45'Π_18 (coe v0) (coe v1) (coe v5)
                     (coe
                        (\ v8 ->
                           coe
                             v4
                             (coe
                                MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                                v6 v8)
                             (coe
                                MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                                v7 v8)))))
      _ -> MAlonzo.RTE.mazUnreachableError
