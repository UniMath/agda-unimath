{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QwZ45Ztypes where

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
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QalgebrasZ45ZpolynomialZ45Zendofunctors
import qualified MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes

-- foundation.w-types.𝕎
d_𝕎_12 a0 a1 a2 a3 = ()
data T_𝕎_12 = C_tree'45'𝕎_26 AgdaAny (AgdaAny -> T_𝕎_12)
-- foundation.w-types._.symbol-𝕎
d_symbol'45'𝕎_40 :: T_𝕎_12 -> AgdaAny
d_symbol'45'𝕎_40 v0
  = case coe v0 of
      C_tree'45'𝕎_26 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.w-types._.component-𝕎
d_component'45'𝕎_48 :: T_𝕎_12 -> AgdaAny -> T_𝕎_12
d_component'45'𝕎_48 v0
  = case coe v0 of
      C_tree'45'𝕎_26 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.w-types._.η-𝕎
d_η'45'𝕎_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_η'45'𝕎_56 = erased
-- foundation.w-types._.constant-𝕎
d_constant'45'𝕎_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  T_𝕎_12
d_constant'45'𝕎_76 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_constant'45'𝕎_76 v4 v5
du_constant'45'𝕎_76 ::
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  T_𝕎_12
du_constant'45'𝕎_76 v0 v1
  = coe
      C_tree'45'𝕎_26 (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
         (coe
            (\ v2 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18))
         (coe v1))
-- foundation.w-types._.is-constant-𝕎
d_is'45'constant'45'𝕎_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> T_𝕎_12 -> ()
d_is'45'constant'45'𝕎_82 = erased
-- foundation.w-types._.is-empty-𝕎
d_is'45'empty'45'𝕎_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'𝕎_100 = erased
-- foundation.w-types._.Eq-𝕎
d_Eq'45'𝕎_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> T_𝕎_12 -> T_𝕎_12 -> ()
d_Eq'45'𝕎_122 = erased
-- foundation.w-types._.refl-Eq-𝕎
d_refl'45'Eq'45'𝕎_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> T_𝕎_12 -> AgdaAny
d_refl'45'Eq'45'𝕎_138 ~v0 ~v1 ~v2 ~v3 v4
  = du_refl'45'Eq'45'𝕎_138 v4
du_refl'45'Eq'45'𝕎_138 :: T_𝕎_12 -> AgdaAny
du_refl'45'Eq'45'𝕎_138 v0
  = case coe v0 of
      C_tree'45'𝕎_26 v1 v2
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
             erased (coe (\ v3 -> coe du_refl'45'Eq'45'𝕎_138 (coe v2 v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.w-types._.center-total-Eq-𝕎
d_center'45'total'45'Eq'45'𝕎_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_center'45'total'45'Eq'45'𝕎_148 ~v0 ~v1 ~v2 ~v3 v4
  = du_center'45'total'45'Eq'45'𝕎_148 v4
du_center'45'total'45'Eq'45'𝕎_148 ::
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_center'45'total'45'Eq'45'𝕎_148 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe v0) (coe du_refl'45'Eq'45'𝕎_138 (coe v0))
-- foundation.w-types._.aux-total-Eq-𝕎
d_aux'45'total'45'Eq'45'𝕎_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> T_𝕎_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_aux'45'total'45'Eq'45'𝕎_160 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_aux'45'total'45'Eq'45'𝕎_160 v4 v6
du_aux'45'total'45'Eq'45'𝕎_160 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_aux'45'total'45'Eq'45'𝕎_160 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
             (coe C_tree'45'𝕎_26 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                erased (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.w-types._.contraction-total-Eq-𝕎
d_contraction'45'total'45'Eq'45'𝕎_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_contraction'45'total'45'Eq'45'𝕎_174 = erased
-- foundation.w-types._.is-contr-total-Eq-𝕎
d_is'45'contr'45'total'45'Eq'45'𝕎_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'Eq'45'𝕎_196 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'contr'45'total'45'Eq'45'𝕎_196 v4
du_is'45'contr'45'total'45'Eq'45'𝕎_196 ::
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'Eq'45'𝕎_196 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_center'45'total'45'Eq'45'𝕎_148 (coe v0)) erased
-- foundation.w-types._.Eq-𝕎-eq
d_Eq'45'𝕎'45'eq_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  T_𝕎_12 ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_Eq'45'𝕎'45'eq_204 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_Eq'45'𝕎'45'eq_204 v4
du_Eq'45'𝕎'45'eq_204 :: T_𝕎_12 -> AgdaAny
du_Eq'45'𝕎'45'eq_204 v0 = coe du_refl'45'Eq'45'𝕎_138 (coe v0)
-- foundation.w-types._.is-equiv-Eq-𝕎-eq
d_is'45'equiv'45'Eq'45'𝕎'45'eq_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  T_𝕎_12 ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'Eq'45'𝕎'45'eq_212 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'equiv'45'Eq'45'𝕎'45'eq_212 v4
du_is'45'equiv'45'Eq'45'𝕎'45'eq_212 ::
  T_𝕎_12 ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'Eq'45'𝕎'45'eq_212 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation.w-types._.eq-Eq-𝕎
d_eq'45'Eq'45'𝕎_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  T_𝕎_12 ->
  T_𝕎_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'Eq'45'𝕎_220 = erased
-- foundation.w-types._.equiv-Eq-𝕎-eq
d_equiv'45'Eq'45'𝕎'45'eq_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  T_𝕎_12 ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'Eq'45'𝕎'45'eq_230 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_equiv'45'Eq'45'𝕎'45'eq_230 v4 v5
du_equiv'45'Eq'45'𝕎'45'eq_230 ::
  T_𝕎_12 ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'Eq'45'𝕎'45'eq_230 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (\ v2 -> coe du_Eq'45'𝕎'45'eq_204 (coe v0))
      (coe du_is'45'equiv'45'Eq'45'𝕎'45'eq_212 v0 v1)
-- foundation.w-types._.is-trunc-𝕎
d_is'45'trunc'45'𝕎_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_𝕎_12 -> T_𝕎_12 -> AgdaAny
d_is'45'trunc'45'𝕎_238 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_is'45'trunc'45'𝕎_238 v1 v4 v5 v6 v7
du_is'45'trunc'45'𝕎_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_𝕎_12 -> T_𝕎_12 -> AgdaAny
du_is'45'trunc'45'𝕎_238 v0 v1 v2 v3 v4
  = case coe v3 of
      C_tree'45'𝕎_26 v5 v6
        -> case coe v4 of
             C_tree'45'𝕎_26 v7 v8
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'is'45'equiv_184
                    v1 (\ v9 -> coe du_Eq'45'𝕎'45'eq_204 (coe v3))
                    (coe du_is'45'equiv'45'Eq'45'𝕎'45'eq_212 v3 v4)
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'Σ_318
                       (coe v1) (coe v2 v5 v7)
                       (coe
                          (\ v9 ->
                             coe
                               MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes.du_is'45'trunc'45'Π_18
                               (coe v0) (coe ()) (coe v1)
                               (coe
                                  (\ v10 ->
                                     coe
                                       MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'is'45'equiv''_228
                                       (coe v1) (\ v11 -> coe du_Eq'45'𝕎'45'eq_204 (coe v6 v10))
                                       (coe
                                          du_is'45'equiv'45'Eq'45'𝕎'45'eq_212 (coe v6 v10)
                                          (coe v8 v10))
                                       (coe
                                          du_is'45'trunc'45'𝕎_238 (coe v0) (coe v1) (coe v2)
                                          (coe v6 v10) (coe v8 v10)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.w-types.structure-𝕎-Alg
d_structure'45'𝕎'45'Alg_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  T_𝕎_12
d_structure'45'𝕎'45'Alg_264 ~v0 ~v1 ~v2 ~v3 v4
  = du_structure'45'𝕎'45'Alg_264 v4
du_structure'45'𝕎'45'Alg_264 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  T_𝕎_12
du_structure'45'𝕎'45'Alg_264 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> coe C_tree'45'𝕎_26 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.w-types.𝕎-Alg
d_𝕎'45'Alg_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_𝕎'45'Alg_278 ~v0 ~v1 ~v2 ~v3 = du_𝕎'45'Alg_278
du_𝕎'45'Alg_278 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_𝕎'45'Alg_278
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_structure'45'𝕎'45'Alg_264)
-- foundation.w-types.map-inv-structure-𝕎-Alg
d_map'45'inv'45'structure'45'𝕎'45'Alg_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'structure'45'𝕎'45'Alg_292 ~v0 ~v1 ~v2 ~v3 v4
  = du_map'45'inv'45'structure'45'𝕎'45'Alg_292 v4
du_map'45'inv'45'structure'45'𝕎'45'Alg_292 ::
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'structure'45'𝕎'45'Alg_292 v0
  = case coe v0 of
      C_tree'45'𝕎_26 v1 v2
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
             (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.w-types.issec-map-inv-structure-𝕎-Alg
d_issec'45'map'45'inv'45'structure'45'𝕎'45'Alg_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'structure'45'𝕎'45'Alg_306 = erased
-- foundation.w-types.isretr-map-inv-structure-𝕎-Alg
d_isretr'45'map'45'inv'45'structure'45'𝕎'45'Alg_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'structure'45'𝕎'45'Alg_320 = erased
-- foundation.w-types.is-equiv-structure-𝕎-Alg
d_is'45'equiv'45'structure'45'𝕎'45'Alg_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'structure'45'𝕎'45'Alg_334 ~v0 ~v1 ~v2 ~v3
  = du_is'45'equiv'45'structure'45'𝕎'45'Alg_334
du_is'45'equiv'45'structure'45'𝕎'45'Alg_334 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'structure'45'𝕎'45'Alg_334
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'structure'45'𝕎'45'Alg_292) erased erased
-- foundation.w-types.equiv-structure-𝕎-Alg
d_equiv'45'structure'45'𝕎'45'Alg_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'structure'45'𝕎'45'Alg_344 ~v0 ~v1 ~v2 ~v3
  = du_equiv'45'structure'45'𝕎'45'Alg_344
du_equiv'45'structure'45'𝕎'45'Alg_344 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'structure'45'𝕎'45'Alg_344
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_structure'45'𝕎'45'Alg_264)
      (coe du_is'45'equiv'45'structure'45'𝕎'45'Alg_334)
-- foundation.w-types.is-equiv-map-inv-structure-𝕎-Alg
d_is'45'equiv'45'map'45'inv'45'structure'45'𝕎'45'Alg_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'inv'45'structure'45'𝕎'45'Alg_354 ~v0 ~v1
                                                         ~v2 ~v3
  = du_is'45'equiv'45'map'45'inv'45'structure'45'𝕎'45'Alg_354
du_is'45'equiv'45'map'45'inv'45'structure'45'𝕎'45'Alg_354 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'inv'45'structure'45'𝕎'45'Alg_354
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_structure'45'𝕎'45'Alg_264) erased erased
-- foundation.w-types.inv-equiv-structure-𝕎-Alg
d_inv'45'equiv'45'structure'45'𝕎'45'Alg_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'equiv'45'structure'45'𝕎'45'Alg_364 ~v0 ~v1 ~v2 ~v3
  = du_inv'45'equiv'45'structure'45'𝕎'45'Alg_364
du_inv'45'equiv'45'structure'45'𝕎'45'Alg_364 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'equiv'45'structure'45'𝕎'45'Alg_364
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'inv'45'structure'45'𝕎'45'Alg_292)
      (coe du_is'45'equiv'45'map'45'inv'45'structure'45'𝕎'45'Alg_354)
-- foundation.w-types.map-hom-𝕎-Alg
d_map'45'hom'45'𝕎'45'Alg_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  T_𝕎_12 -> AgdaAny
d_map'45'hom'45'𝕎'45'Alg_378 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_map'45'hom'45'𝕎'45'Alg_378 v5 v6
du_map'45'hom'45'𝕎'45'Alg_378 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  T_𝕎_12 -> AgdaAny
du_map'45'hom'45'𝕎'45'Alg_378 v0 v1
  = case coe v1 of
      C_tree'45'𝕎_26 v2 v3
        -> coe
             MAlonzo.Code.Qfoundation.QalgebrasZ45ZpolynomialZ45Zendofunctors.du_structure'45'algebra'45'polynomial'45'endofunctor_50
             v0
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                (coe v2)
                (coe
                   (\ v4 -> coe du_map'45'hom'45'𝕎'45'Alg_378 (coe v0) (coe v3 v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.w-types.structure-hom-𝕎-Alg
d_structure'45'hom'45'𝕎'45'Alg_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_structure'45'hom'45'𝕎'45'Alg_400 = erased
-- foundation.w-types.hom-𝕎-Alg
d_hom'45'𝕎'45'Alg_420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_hom'45'𝕎'45'Alg_420 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_hom'45'𝕎'45'Alg_420 v5
du_hom'45'𝕎'45'Alg_420 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_hom'45'𝕎'45'Alg_420 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'hom'45'𝕎'45'Alg_378 (coe v0)) erased
-- foundation.w-types.htpy-htpy-hom-𝕎-Alg
d_htpy'45'htpy'45'hom'45'𝕎'45'Alg_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  T_𝕎_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_htpy'45'htpy'45'hom'45'𝕎'45'Alg_438 = erased
-- foundation.w-types.compute-structure-htpy-hom-𝕎-Alg
d_compute'45'structure'45'htpy'45'hom'45'𝕎'45'Alg_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  (AgdaAny -> T_𝕎_12) ->
  (T_𝕎_12 -> AgdaAny) ->
  (T_𝕎_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_compute'45'structure'45'htpy'45'hom'45'𝕎'45'Alg_478 = erased
-- foundation.w-types.structure-htpy-hom-𝕎-Alg
d_structure'45'htpy'45'hom'45'𝕎'45'Alg_512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_structure'45'htpy'45'hom'45'𝕎'45'Alg_512 = erased
-- foundation.w-types.htpy-hom-𝕎-Alg
d_htpy'45'hom'45'𝕎'45'Alg_546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_htpy'45'hom'45'𝕎'45'Alg_546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_htpy'45'hom'45'𝕎'45'Alg_546
du_htpy'45'hom'45'𝕎'45'Alg_546 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_htpy'45'hom'45'𝕎'45'Alg_546
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased erased
-- foundation.w-types.is-initial-𝕎-Alg
d_is'45'initial'45'𝕎'45'Alg_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'initial'45'𝕎'45'Alg_564 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_is'45'initial'45'𝕎'45'Alg_564 v5
du_is'45'initial'45'𝕎'45'Alg_564 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'initial'45'𝕎'45'Alg_564 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_hom'45'𝕎'45'Alg_420 (coe v0)) erased
