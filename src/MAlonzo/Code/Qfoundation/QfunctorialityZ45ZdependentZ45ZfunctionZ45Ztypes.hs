{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs
import qualified MAlonzo.Code.Qfoundation.Qequivalences
import qualified MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality
import qualified MAlonzo.Code.Qfoundation.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZunitZ45Ztype

-- foundation.functoriality-dependent-function-types.htpy-map-Π
d_htpy'45'map'45'Π_26 ::
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
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_htpy'45'map'45'Π_26 = erased
-- foundation.functoriality-dependent-function-types.htpy-map-Π'
d_htpy'45'map'45'Π''_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_htpy'45'map'45'Π''_60 = erased
-- foundation.functoriality-dependent-function-types.equiv-fib-map-Π
d_equiv'45'fib'45'map'45'Π_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'fib'45'map'45'Π_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_equiv'45'fib'45'map'45'Π_90
du_equiv'45'fib'45'map'45'Π_90 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'fib'45'map'45'Π_90
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v0 ->
               coe
                 MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality.du_equiv'45'eq'45'htpy_120)))
      (coe
         MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs.du_distributive'45'Π'45'Σ_248)
-- foundation.functoriality-dependent-function-types.is-trunc-map-map-Π
d_is'45'trunc'45'map'45'map'45'Π_118 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny
d_is'45'trunc'45'map'45'map'45'Π_118 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                     v8 v9
  = du_is'45'trunc'45'map'45'map'45'Π_118 v0 v1 v8 v9
du_is'45'trunc'45'map'45'map'45'Π_118 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny
du_is'45'trunc'45'map'45'map'45'Π_118 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'equiv''_252
      v0 (coe du_equiv'45'fib'45'map'45'Π_90)
      (coe
         MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes.du_is'45'trunc'45'Π_18
         (coe v1) (coe ()) (coe v0) (coe (\ v4 -> coe v2 v4 (coe v3 v4))))
-- foundation.functoriality-dependent-function-types.is-equiv-map-Π
d_is'45'equiv'45'map'45'Π_152 ::
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
d_is'45'equiv'45'map'45'Π_152 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_is'45'equiv'45'map'45'Π_152 v0 v7
du_is'45'equiv'45'map'45'Π_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'Π_152 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'equiv'45'is'45'contr'45'map_60
      (coe
         du_is'45'trunc'45'map'45'map'45'Π_118
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6)
         (coe v0)
         (coe
            (\ v2 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
                 (coe v1 v2))))
-- foundation.functoriality-dependent-function-types.equiv-map-Π
d_equiv'45'map'45'Π_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'map'45'Π_180 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_equiv'45'map'45'Π_180 v0 v6
du_equiv'45'map'45'Π_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'map'45'Π_180 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du_map'45'Π_154
         (coe
            (\ v2 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                 (coe v1 v2))))
      (coe
         du_is'45'equiv'45'map'45'Π_152 (coe v0)
         (coe
            (\ v2 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
                 (coe v1 v2))))
-- foundation.functoriality-dependent-function-types._.map-equiv-Π
d_map'45'equiv'45'Π_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'45'equiv'45'Π_220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_map'45'equiv'45'Π_220 v8 v9
du_map'45'equiv'45'Π_220 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'45'equiv'45'Π_220 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du_map'45'Π_154
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                      (coe (\ v4 v5 -> v5))
                      (coe
                         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                         (coe
                            v1
                            (coe
                               MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'equiv_240
                               v0 v3)))))))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du_precomp'45'Π_82
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'equiv_240
            (coe v0)))
-- foundation.functoriality-dependent-function-types._.compute-map-equiv-Π
d_compute'45'map'45'equiv'45'Π_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_compute'45'map'45'equiv'45'Π_230 = erased
-- foundation.functoriality-dependent-function-types._._.α
d_α_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_α_244 = erased
-- foundation.functoriality-dependent-function-types._.is-equiv-map-equiv-Π
d_is'45'equiv'45'map'45'equiv'45'Π_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'equiv'45'Π_252 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 v8 v9
  = du_is'45'equiv'45'map'45'equiv'45'Π_252 v2 v8 v9
du_is'45'equiv'45'map'45'equiv'45'Π_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'equiv'45'Π_252 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp''_370
      (coe
         MAlonzo.Code.Qfoundation.Qequivalences.du_is'45'equiv'45'precomp'45'Π'45'is'45'equiv_194
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'is'45'equiv_216
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
               (coe v1)))
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'inv'45'is'45'equiv_224
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
               (coe v1)))
         erased)
      (coe
         du_is'45'equiv'45'map'45'Π_152 (coe v0)
         (coe
            (\ v3 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp''_370
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
                    (coe
                       v2
                       (coe
                          MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'is'45'equiv_216
                          (coe
                             MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
                             (coe v1))
                          v3)))
                 (coe
                    MAlonzo.Code.Qfoundation.QidentityZ45Ztypes.du_is'45'equiv'45'tr_270))))
-- foundation.functoriality-dependent-function-types._.equiv-Π
d_equiv'45'Π_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'Π_262 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_equiv'45'Π_262 v2 v8 v9
du_equiv'45'Π_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'Π_262 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'equiv'45'Π_220 (coe v1) (coe v2))
      (coe
         du_is'45'equiv'45'map'45'equiv'45'Π_252 (coe v0) (coe v1) (coe v2))
-- foundation.functoriality-dependent-function-types.id-map-equiv-Π
d_id'45'map'45'equiv'45'Π_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_id'45'map'45'equiv'45'Π_274 = erased
-- foundation.functoriality-dependent-function-types.equiv-fib-map-Π'
d_equiv'45'fib'45'map'45'Π''_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'fib'45'map'45'Π''_310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10
  = du_equiv'45'fib'45'map'45'Π''_310
du_equiv'45'fib'45'map'45'Π''_310 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'fib'45'map'45'Π''_310
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v0 ->
               coe
                 MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality.du_equiv'45'eq'45'htpy_120)))
      (coe
         MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs.du_distributive'45'Π'45'Σ_248)
-- foundation.functoriality-dependent-function-types.is-trunc-map-map-Π-is-trunc-map'
d_is'45'trunc'45'map'45'map'45'Π'45'is'45'trunc'45'map''_346 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny
d_is'45'trunc'45'map'45'map'45'Π'45'is'45'trunc'45'map''_346 v0 ~v1
                                                             ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 v11
                                                             v12
  = du_is'45'trunc'45'map'45'map'45'Π'45'is'45'trunc'45'map''_346
      v0 v4 v9 v11 v12
du_is'45'trunc'45'map'45'map'45'Π'45'is'45'trunc'45'map''_346 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny
du_is'45'trunc'45'map'45'map'45'Π'45'is'45'trunc'45'map''_346 v0 v1
                                                              v2 v3 v4
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'equiv''_252
      v0 (coe du_equiv'45'fib'45'map'45'Π''_310)
      (coe
         MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes.du_is'45'trunc'45'Π_18
         (coe v1) (coe ()) (coe v0)
         (coe (\ v5 -> coe v3 (coe v2 v5) (coe v4 v5))))
-- foundation.functoriality-dependent-function-types.is-trunc-map-is-trunc-map-map-Π'
d_is'45'trunc'45'map'45'is'45'trunc'45'map'45'map'45'Π''_390 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () -> (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'map'45'is'45'trunc'45'map'45'map'45'Π''_390 v0 ~v1
                                                             ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_is'45'trunc'45'map'45'is'45'trunc'45'map'45'map'45'Π''_390
      v0 v8 v9 v10
du_is'45'trunc'45'map'45'is'45'trunc'45'map'45'map'45'Π''_390 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () -> (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'map'45'is'45'trunc'45'map'45'map'45'Π''_390 v0 v1
                                                              v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'equiv''_252
      v0
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'Σ_544
         (coe
            MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZunitZ45Ztype.du_equiv'45'universal'45'property'45'unit_70)
         (coe
            (\ v4 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_equiv'45'ap_912)))
      (coe v1 () erased (\ v4 -> v2) (\ v4 -> v3))
-- foundation.functoriality-dependent-function-types.HTPY-map-equiv-Π
d_HTPY'45'map'45'equiv'45'Π_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  ()
d_HTPY'45'map'45'equiv'45'Π_438 = erased
-- foundation.functoriality-dependent-function-types.htpy-map-equiv-Π-refl-htpy
d_htpy'45'map'45'equiv'45'Π'45'refl'45'htpy_484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_htpy'45'map'45'equiv'45'Π'45'refl'45'htpy_484 = erased
-- foundation.functoriality-dependent-function-types.htpy-map-equiv-Π
d_htpy'45'map'45'equiv'45'Π_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_htpy'45'map'45'equiv'45'Π_522 = erased
-- foundation.functoriality-dependent-function-types.comp-htpy-map-equiv-Π
d_comp'45'htpy'45'map'45'equiv'45'Π_558 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'htpy'45'map'45'equiv'45'Π_558 = erased
-- foundation.functoriality-dependent-function-types.map-automorphism-Π
d_map'45'automorphism'45'Π_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'45'automorphism'45'Π_584 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_map'45'automorphism'45'Π_584 v4 v5
du_map'45'automorphism'45'Π_584 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'45'automorphism'45'Π_584 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du_map'45'Π_154
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'is'45'equiv_216
                      (coe
                         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
                         (coe v1 v3))))))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du_precomp'45'Π_82
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
            (coe v0)))
-- foundation.functoriality-dependent-function-types.is-equiv-map-automorphism-Π
d_is'45'equiv'45'map'45'automorphism'45'Π_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'automorphism'45'Π_608 v0 ~v1 ~v2 ~v3 v4 v5
  = du_is'45'equiv'45'map'45'automorphism'45'Π_608 v0 v4 v5
du_is'45'equiv'45'map'45'automorphism'45'Π_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'automorphism'45'Π_608 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp''_370
      (coe
         MAlonzo.Code.Qfoundation.Qequivalences.du_is'45'equiv'45'precomp'45'Π'45'is'45'equiv_194
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
            (coe v1))
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
            (coe v1))
         erased)
      (coe
         du_is'45'equiv'45'map'45'Π_152 (coe v0)
         (coe
            (\ v3 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'inv'45'is'45'equiv_224
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                    (coe v2 v3)))))
-- foundation.functoriality-dependent-function-types.automorphism-Π
d_automorphism'45'Π_636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_automorphism'45'Π_636 v0 ~v1 ~v2 ~v3 v4 v5
  = du_automorphism'45'Π_636 v0 v4 v5
du_automorphism'45'Π_636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_automorphism'45'Π_636 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'automorphism'45'Π_584 (coe v1) (coe v2))
      (coe
         du_is'45'equiv'45'map'45'automorphism'45'Π_608 (coe v0) (coe v1)
         (coe v2))
