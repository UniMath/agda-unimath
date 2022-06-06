{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes

-- foundation-core.functoriality-dependent-pair-types._.tot
d_tot_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_tot_24 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_tot_24 v6 v7
du_tot_24 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_tot_24 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe v1))
      (coe
         v0
         (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
            (coe v1))
         (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
            (coe v1)))
-- foundation-core.functoriality-dependent-pair-types._.map-Σ-map-base
d_map'45'Σ'45'map'45'base_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'Σ'45'map'45'base_50 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_map'45'Σ'45'map'45'base_50 v5 v7
du_map'45'Σ'45'map'45'base_50 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'Σ'45'map'45'base_50 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         v0
         (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
            (coe v1)))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
         (coe v1))
-- foundation-core.functoriality-dependent-pair-types._.map-Σ
d_map'45'Σ_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'Σ_82 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_map'45'Σ_82 v8 v9 v10
du_map'45'Σ_82 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'Σ_82 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         v0
         (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
            (coe v2)))
      (coe
         v1
         (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
            (coe v2))
         (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
            (coe v2)))
-- foundation-core.functoriality-dependent-pair-types._.triangle-map-Σ
d_triangle'45'map'45'Σ_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'map'45'Σ_102 = erased
-- foundation-core.functoriality-dependent-pair-types.tot-htpy
d_tot'45'htpy_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_tot'45'htpy_132 = erased
-- foundation-core.functoriality-dependent-pair-types.tot-id
d_tot'45'id_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_tot'45'id_152 = erased
-- foundation-core.functoriality-dependent-pair-types.tot-comp
d_tot'45'comp_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_tot'45'comp_186 = erased
-- foundation-core.functoriality-dependent-pair-types._.map-compute-fib-tot
d_map'45'compute'45'fib'45'tot_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'compute'45'fib'45'tot_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   v8
  = du_map'45'compute'45'fib'45'tot_218 v8
du_map'45'compute'45'fib'45'tot_218 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'compute'45'fib'45'tot_218 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                  -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- foundation-core.functoriality-dependent-pair-types._.map-inv-compute-fib-tot
d_map'45'inv'45'compute'45'fib'45'tot_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'compute'45'fib'45'tot_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                          ~v6 v7 v8
  = du_map'45'inv'45'compute'45'fib'45'tot_230 v7 v8
du_map'45'inv'45'compute'45'fib'45'tot_230 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'compute'45'fib'45'tot_230 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
              -> coe seq (coe v1) (coe v2)
            _ -> MAlonzo.RTE.mazUnreachableError)
         (coe
            seq (coe v0)
            (case coe v1 of
               MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
                 -> coe v2
               _ -> MAlonzo.RTE.mazUnreachableError)))
      erased
-- foundation-core.functoriality-dependent-pair-types._.issec-map-inv-compute-fib-tot
d_issec'45'map'45'inv'45'compute'45'fib'45'tot_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'compute'45'fib'45'tot_246 = erased
-- foundation-core.functoriality-dependent-pair-types._.isretr-map-inv-compute-fib-tot
d_isretr'45'map'45'inv'45'compute'45'fib'45'tot_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'compute'45'fib'45'tot_254 = erased
-- foundation-core.functoriality-dependent-pair-types._.is-equiv-map-compute-fib-tot
d_is'45'equiv'45'map'45'compute'45'fib'45'tot_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'compute'45'fib'45'tot_262 ~v0 ~v1 ~v2 ~v3
                                                  ~v4 ~v5 ~v6 v7
  = du_is'45'equiv'45'map'45'compute'45'fib'45'tot_262 v7
du_is'45'equiv'45'map'45'compute'45'fib'45'tot_262 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'compute'45'fib'45'tot_262 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'compute'45'fib'45'tot_230 (coe v0)) erased
      erased
-- foundation-core.functoriality-dependent-pair-types._.compute-fib-tot
d_compute'45'fib'45'tot_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_compute'45'fib'45'tot_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_compute'45'fib'45'tot_268 v7
du_compute'45'fib'45'tot_268 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_compute'45'fib'45'tot_268 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'compute'45'fib'45'tot_218)
      (coe du_is'45'equiv'45'map'45'compute'45'fib'45'tot_262 (coe v0))
-- foundation-core.functoriality-dependent-pair-types._.is-equiv-map-inv-compute-fib-tot
d_is'45'equiv'45'map'45'inv'45'compute'45'fib'45'tot_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'inv'45'compute'45'fib'45'tot_276 ~v0 ~v1
                                                         ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_is'45'equiv'45'map'45'inv'45'compute'45'fib'45'tot_276
du_is'45'equiv'45'map'45'inv'45'compute'45'fib'45'tot_276 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'inv'45'compute'45'fib'45'tot_276
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'compute'45'fib'45'tot_218) erased erased
-- foundation-core.functoriality-dependent-pair-types._.inv-compute-fib-tot
d_inv'45'compute'45'fib'45'tot_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'compute'45'fib'45'tot_282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inv'45'compute'45'fib'45'tot_282 v7
du_inv'45'compute'45'fib'45'tot_282 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'compute'45'fib'45'tot_282 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'inv'45'compute'45'fib'45'tot_230 (coe v0))
      (coe du_is'45'equiv'45'map'45'inv'45'compute'45'fib'45'tot_276)
-- foundation-core.functoriality-dependent-pair-types._.is-equiv-tot-is-fiberwise-equiv
d_is'45'equiv'45'tot'45'is'45'fiberwise'45'equiv_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'tot'45'is'45'fiberwise'45'equiv_308 ~v0 ~v1 ~v2
                                                     ~v3 ~v4 ~v5 ~v6 v7
  = du_is'45'equiv'45'tot'45'is'45'fiberwise'45'equiv_308 v7
du_is'45'equiv'45'tot'45'is'45'fiberwise'45'equiv_308 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'tot'45'is'45'fiberwise'45'equiv_308 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'equiv'45'is'45'contr'45'map_60
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'is'45'equiv_162
              (coe du_is'45'equiv'45'map'45'compute'45'fib'45'tot_262 (coe v1))
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
                 (coe
                    v0
                    (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                       (coe v1)))
                 (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
                    (coe v1)))))
-- foundation-core.functoriality-dependent-pair-types._.is-fiberwise-equiv-is-equiv-tot
d_is'45'fiberwise'45'equiv'45'is'45'equiv'45'tot_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'fiberwise'45'equiv'45'is'45'equiv'45'tot_314 ~v0 ~v1 ~v2
                                                     ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'tot_314 v7 v8
du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'tot_314 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'tot_314 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'equiv'45'is'45'contr'45'map_60
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'is'45'equiv''_206
              (coe du_map'45'compute'45'fib'45'tot_218)
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
                 v0
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                    (coe v1) (coe v2)))))
-- foundation-core.functoriality-dependent-pair-types._.equiv-tot
d_equiv'45'tot_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'tot_340 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_equiv'45'tot_340 v6
du_equiv'45'tot_340 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'tot_340 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         du_tot_24
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                 (coe v0 v1))))
      (coe
         du_is'45'equiv'45'tot'45'is'45'fiberwise'45'equiv_308
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
                 (coe v0 v1))))
-- foundation-core.functoriality-dependent-pair-types._.fib-map-Σ-map-base-fib
d_fib'45'map'45'Σ'45'map'45'base'45'fib_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_fib'45'map'45'Σ'45'map'45'base'45'fib_370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                            ~v6 v7 v8
  = du_fib'45'map'45'Σ'45'map'45'base'45'fib_370 v7 v8
du_fib'45'map'45'Σ'45'map'45'base'45'fib_370 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_fib'45'map'45'Σ'45'map'45'base'45'fib_370 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe
            seq (coe v0)
            (case coe v1 of
               MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
                 -> coe v2
               _ -> MAlonzo.RTE.mazUnreachableError))
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
              -> coe seq (coe v1) (coe v3)
            _ -> MAlonzo.RTE.mazUnreachableError))
      erased
-- foundation-core.functoriality-dependent-pair-types._.fib-fib-map-Σ-map-base
d_fib'45'fib'45'map'45'Σ'45'map'45'base_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_fib'45'fib'45'map'45'Σ'45'map'45'base_386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7 v8
  = du_fib'45'fib'45'map'45'Σ'45'map'45'base_386 v8
du_fib'45'fib'45'map'45'Σ'45'map'45'base_386 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_fib'45'fib'45'map'45'Σ'45'map'45'base_386 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                  -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- foundation-core.functoriality-dependent-pair-types._.issec-fib-fib-map-Σ-map-base
d_issec'45'fib'45'fib'45'map'45'Σ'45'map'45'base_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'fib'45'fib'45'map'45'Σ'45'map'45'base_398 = erased
-- foundation-core.functoriality-dependent-pair-types._.isretr-fib-fib-map-Σ-map-base
d_isretr'45'fib'45'fib'45'map'45'Σ'45'map'45'base_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'fib'45'fib'45'map'45'Σ'45'map'45'base_406 = erased
-- foundation-core.functoriality-dependent-pair-types._.is-equiv-fib-map-Σ-map-base-fib
d_is'45'equiv'45'fib'45'map'45'Σ'45'map'45'base'45'fib_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'fib'45'map'45'Σ'45'map'45'base'45'fib_414 ~v0 ~v1
                                                           ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_is'45'equiv'45'fib'45'map'45'Σ'45'map'45'base'45'fib_414
du_is'45'equiv'45'fib'45'map'45'Σ'45'map'45'base'45'fib_414 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'fib'45'map'45'Σ'45'map'45'base'45'fib_414
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_fib'45'fib'45'map'45'Σ'45'map'45'base_386) erased erased
-- foundation-core.functoriality-dependent-pair-types._.equiv-fib-map-Σ-map-base-fib
d_equiv'45'fib'45'map'45'Σ'45'map'45'base'45'fib_420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'fib'45'map'45'Σ'45'map'45'base'45'fib_420 ~v0 ~v1 ~v2
                                                     ~v3 ~v4 ~v5 ~v6 v7
  = du_equiv'45'fib'45'map'45'Σ'45'map'45'base'45'fib_420 v7
du_equiv'45'fib'45'map'45'Σ'45'map'45'base'45'fib_420 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'fib'45'map'45'Σ'45'map'45'base'45'fib_420 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_fib'45'map'45'Σ'45'map'45'base'45'fib_370 (coe v0))
      (coe du_is'45'equiv'45'fib'45'map'45'Σ'45'map'45'base'45'fib_414)
-- foundation-core.functoriality-dependent-pair-types._.is-contr-map-map-Σ-map-base
d_is'45'contr'45'map'45'map'45'Σ'45'map'45'base_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'map'45'map'45'Σ'45'map'45'base_444 ~v0 ~v1 ~v2 ~v3
                                                    ~v4 ~v5 ~v6 v7 v8
  = du_is'45'contr'45'map'45'map'45'Σ'45'map'45'base_444 v7 v8
du_is'45'contr'45'map'45'map'45'Σ'45'map'45'base_444 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'map'45'map'45'Σ'45'map'45'base_444 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
             (coe
                du_equiv'45'fib'45'map'45'Σ'45'map'45'base'45'fib_420 (coe v1))
             (coe v0 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.functoriality-dependent-pair-types._.is-equiv-map-Σ-map-base
d_is'45'equiv'45'map'45'Σ'45'map'45'base_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'Σ'45'map'45'base_470 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 v7
  = du_is'45'equiv'45'map'45'Σ'45'map'45'base_470 v7
du_is'45'equiv'45'map'45'Σ'45'map'45'base_470 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'Σ'45'map'45'base_470 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'equiv'45'is'45'contr'45'map_60
      (coe
         du_is'45'contr'45'map'45'map'45'Σ'45'map'45'base_444
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
            v0))
-- foundation-core.functoriality-dependent-pair-types.equiv-Σ-equiv-base
d_equiv'45'Σ'45'equiv'45'base_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'Σ'45'equiv'45'base_488 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_equiv'45'Σ'45'equiv'45'base_488 v6
du_equiv'45'Σ'45'equiv'45'base_488 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'Σ'45'equiv'45'base_488 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe du_map'45'Σ'45'map'45'base_50 (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe du_is'45'equiv'45'map'45'Σ'45'map'45'base_470 (coe v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- foundation-core.functoriality-dependent-pair-types._.is-equiv-map-Σ
d_is'45'equiv'45'map'45'Σ_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'Σ_528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 v10 v11
  = du_is'45'equiv'45'map'45'Σ_528 v10 v11
du_is'45'equiv'45'map'45'Σ_528 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'Σ_528 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp_332
      (coe
         du_is'45'equiv'45'tot'45'is'45'fiberwise'45'equiv_308 (coe v1))
      (coe du_is'45'equiv'45'map'45'Σ'45'map'45'base_470 (coe v0))
-- foundation-core.functoriality-dependent-pair-types._.equiv-Σ
d_equiv'45'Σ_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'Σ_544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_equiv'45'Σ_544 v8 v9
du_equiv'45'Σ_544 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'Σ_544 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         du_map'45'Σ_82
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
            (coe v0))
         (coe
            (\ v2 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                 (coe v1 v2))))
      (coe
         du_is'45'equiv'45'map'45'Σ_528
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
            (coe v0))
         (coe
            (\ v2 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
                 (coe v1 v2))))
-- foundation-core.functoriality-dependent-pair-types._.is-fiberwise-equiv-is-equiv-map-Σ
d_is'45'fiberwise'45'equiv'45'is'45'equiv'45'map'45'Σ_566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'fiberwise'45'equiv'45'is'45'equiv'45'map'45'Σ_566 ~v0 ~v1
                                                          ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 v10 v11
  = du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'map'45'Σ_566
      v8 v10 v11
du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'map'45'Σ_566 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'map'45'Σ_566 v0 v1 v2
  = coe
      du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'tot_314
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'right'45'factor_458
         (coe du_map'45'Σ'45'map'45'base_50 (coe v0))
         (coe du_is'45'equiv'45'map'45'Σ'45'map'45'base_470 (coe v1))
         (coe v2))
-- foundation-core.functoriality-dependent-pair-types._.fib-triangle
d_fib'45'triangle_602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_fib'45'triangle_602 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                      v11
  = du_fib'45'triangle_602 v8 v11
du_fib'45'triangle_602 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_fib'45'triangle_602 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v1 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> coe v0 v2
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- foundation-core.functoriality-dependent-pair-types._.square-tot-fib-triangle
d_square'45'tot'45'fib'45'triangle_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_square'45'tot'45'fib'45'triangle_608 = erased
-- foundation-core.functoriality-dependent-pair-types._.is-fiberwise-equiv-is-equiv-triangle
d_is'45'fiberwise'45'equiv'45'is'45'equiv'45'triangle_638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'fiberwise'45'equiv'45'is'45'equiv'45'triangle_638 ~v0 ~v1
                                                          ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10
  = du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'triangle_638
      v6 v7 v10
du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'triangle_638 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'triangle_638 v0 v1 v2
  = coe
      du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'tot_314
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'top'45'is'45'equiv'45'bottom'45'square_828
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_map'45'equiv'45'total'45'fib_214)
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_is'45'equiv'45'map'45'equiv'45'total'45'fib_234
            (coe v0))
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_is'45'equiv'45'map'45'equiv'45'total'45'fib_234
            (coe v1))
         (coe v2))
-- foundation-core.functoriality-dependent-pair-types._.is-equiv-triangle-is-fiberwise-equiv
d_is'45'equiv'45'triangle'45'is'45'fiberwise'45'equiv_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'triangle'45'is'45'fiberwise'45'equiv_642 ~v0 ~v1
                                                          ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10
  = du_is'45'equiv'45'triangle'45'is'45'fiberwise'45'equiv_642
      v6 v7 v10
du_is'45'equiv'45'triangle'45'is'45'fiberwise'45'equiv_642 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'triangle'45'is'45'fiberwise'45'equiv_642 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'bottom'45'is'45'equiv'45'top'45'square_836
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_map'45'equiv'45'total'45'fib_214)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_is'45'equiv'45'map'45'equiv'45'total'45'fib_234
         (coe v0))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_is'45'equiv'45'map'45'equiv'45'total'45'fib_234
         (coe v1))
      (coe
         du_is'45'equiv'45'tot'45'is'45'fiberwise'45'equiv_308 (coe v2))
