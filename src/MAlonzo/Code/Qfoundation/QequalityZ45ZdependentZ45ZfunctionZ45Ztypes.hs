{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QequalityZ45ZdependentZ45ZfunctionZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs

-- foundation.equality-dependent-function-types.is-contr-total-Eq-Π
d_is'45'contr'45'total'45'Eq'45'Π_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'Eq'45'Π_28 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_is'45'contr'45'total'45'Eq'45'Π_28 v0 v6
du_is'45'contr'45'total'45'Eq'45'Π_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'Eq'45'Π_28 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
      (coe
         MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs.du_distributive'45'Π'45'Σ_248)
      (coe
         MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes.du_is'45'contr'45'Π_16
         (coe v0) (coe ()) (coe v1))
-- foundation.equality-dependent-function-types._.map-extensionality-Π
d_map'45'extensionality'45'Π_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny -> AgdaAny
d_map'45'extensionality'45'Π_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
                                ~v9 v10
  = du_map'45'extensionality'45'Π_72 v7 v8 v10
du_map'45'extensionality'45'Π_72 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'45'extensionality'45'Π_72 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe v0 v2 (coe v1 v2)) erased
-- foundation.equality-dependent-function-types._.is-equiv-map-extensionality-Π
d_is'45'equiv'45'map'45'extensionality'45'Π_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'extensionality'45'Π_88 ~v0 ~v1 ~v2 ~v3 ~v4
                                               v5 ~v6 ~v7
  = du_is'45'equiv'45'map'45'extensionality'45'Π_88 v5
du_is'45'equiv'45'map'45'extensionality'45'Π_88 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'extensionality'45'Π_88 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation.equality-dependent-function-types._.extensionality-Π
d_extensionality'45'Π_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_extensionality'45'Π_108 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8
  = du_extensionality'45'Π_108 v5 v7 v8
du_extensionality'45'Π_108 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_extensionality'45'Π_108 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (\ v3 v4 ->
         coe du_map'45'extensionality'45'Π_72 (coe v1) (coe v2) v4)
      (coe du_is'45'equiv'45'map'45'extensionality'45'Π_88 v0 v2)
