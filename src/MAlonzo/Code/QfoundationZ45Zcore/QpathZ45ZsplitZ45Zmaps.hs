{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.QpathZ45ZsplitZ45Zmaps where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions

-- foundation-core.path-split-maps._.is-path-split
d_is'45'path'45'split_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> (AgdaAny -> AgdaAny) -> ()
d_is'45'path'45'split_18 = erased
-- foundation-core.path-split-maps._.is-path-split-is-equiv
d_is'45'path'45'split'45'is'45'equiv_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'path'45'split'45'is'45'equiv_38 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_is'45'path'45'split'45'is'45'equiv_38 v5
du_is'45'path'45'split'45'is'45'equiv_38 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'path'45'split'45'is'45'equiv_38 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe v0))
      (coe
         (\ v1 v2 ->
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'emb'45'is'45'equiv_878)))
-- foundation-core.path-split-maps._.is-coherently-invertible-is-path-split
d_is'45'coherently'45'invertible'45'is'45'path'45'split_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'coherently'45'invertible'45'is'45'path'45'split_48 ~v0 ~v1
                                                           ~v2 ~v3 v4 v5
  = du_is'45'coherently'45'invertible'45'is'45'path'45'split_48 v4 v5
du_is'45'coherently'45'invertible'45'is'45'path'45'split_48 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'coherently'45'invertible'45'is'45'path'45'split_48 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v1 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> case coe v2 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                  -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (case coe v1 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
              -> case coe v2 of
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                     -> coe v5
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError)
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
            (case coe v1 of
               MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
                 -> case coe v2 of
                      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                        -> coe
                             (\ v6 ->
                                coe
                                  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                                  (coe v3 (coe v4 (coe v0 v6)) v6) (coe v5 (coe v0 v6)))
                      _ -> MAlonzo.RTE.mazUnreachableError
               _ -> MAlonzo.RTE.mazUnreachableError)
            erased))
-- foundation-core.path-split-maps._.is-equiv-is-path-split
d_is'45'equiv'45'is'45'path'45'split_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'path'45'split_78 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'equiv'45'is'45'path'45'split_78 v4
du_is'45'equiv'45'is'45'path'45'split_78 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'path'45'split_78 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'is'45'coherently'45'invertible_190))
      (coe
         du_is'45'coherently'45'invertible'45'is'45'path'45'split_48
         (coe v0))
