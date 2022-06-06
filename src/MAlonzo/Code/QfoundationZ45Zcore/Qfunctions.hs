{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.Qfunctions where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- foundation-core.functions.id
d_id_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> AgdaAny
d_id_8 ~v0 ~v1 v2 = du_id_8 v2
du_id_8 :: AgdaAny -> AgdaAny
du_id_8 v0 = coe v0
-- foundation-core.functions._∘_
d__'8728'__36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'8728'__36 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du__'8728'__36 v6 v7 v8
du__'8728'__36 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'8728'__36 v0 v1 v2 = coe v0 v2 (coe v1 v2)
-- foundation-core.functions.ev-pt
d_ev'45'pt_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> AgdaAny
d_ev'45'pt_56 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_ev'45'pt_56 v3 v5
du_ev'45'pt_56 :: AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_ev'45'pt_56 v0 v1 = coe v1 v0
-- foundation-core.functions.precomp-Π
d_precomp'45'Π_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_precomp'45'Π_82 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8
  = du_precomp'45'Π_82 v5 v7 v8
du_precomp'45'Π_82 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_precomp'45'Π_82 v0 v1 v2 = coe v1 (coe v0 v2)
-- foundation-core.functions.precomp
d_precomp_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_precomp_106 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_precomp_106 v5
du_precomp_106 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_precomp_106 v0 = coe du_precomp'45'Π_82 (coe v0)
-- foundation-core.functions.postcomp
d_postcomp_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_postcomp_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_postcomp_126 v6 v7
du_postcomp_126 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_postcomp_126 v0 v1
  = coe du__'8728'__36 (coe (\ v2 -> v0)) (coe v1)
-- foundation-core.functions.map-Π
d_map'45'Π_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'45'Π_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_map'45'Π_154 v6 v7 v8
du_map'45'Π_154 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'45'Π_154 v0 v1 v2 = coe v0 v2 (coe v1 v2)
-- foundation-core.functions.map-Π'
d_map'45'Π''_186 ::
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
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'45'Π''_186 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_map'45'Π''_186 v8 v9
du_map'45'Π''_186 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'45'Π''_186 v0 v1
  = coe du_map'45'Π_154 (coe (\ v2 -> coe v1 (coe v0 v2)))
