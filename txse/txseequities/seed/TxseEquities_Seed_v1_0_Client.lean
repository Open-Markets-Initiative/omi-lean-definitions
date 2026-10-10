import Wire
import Std.Tactic.BVDecide

/-!
# Texas Stock Exchange Session Enabled Entry Daemon v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TxseTxseequitiesSeedRakeV10Client

/-- Logon Request Packet: 32 bytes -/
structure LogonRequestPacket where
  session : BitVec 64
  senderComp : Alpha 8
  token : Alpha 8
  nextSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LogonRequestPacket

def encode (message : LogonRequestPacket) : List UInt8 :=
  encodeUIntLE 8 message.session
    ++ (Alpha.encode message.senderComp
    ++ (Alpha.encode message.token
    ++ (encodeUIntLE 8 message.nextSequenceNumber)))

def decode (bytes : List UInt8) : Option (LogonRequestPacket × List UInt8) := do
  let (session, bytes) ← decodeUIntLE 8 bytes
  let (senderComp, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← Alpha.decode 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ session, senderComp, token, nextSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LogonRequestPacket) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : LogonRequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogonRequestPacket

/-- Limit Order Message -/
structure LimitOrderMessage where
  limitOrderPresenceBits : Masked 32 8191
  clOrdId : BitVec 64
  orderQty : BitVec 32
  limitOrderBitFields : BitVec 32
  symbolId : BitVec 16
  price : BitVec 64
  limitOrderSelfMatchScope : Option (BitVec 8)
  limitOrderSelfMatchInstruction : Option (BitVec 8)
  limitOrderPriceSlideInstruction : Option (BitVec 8)
  limitOrderMinQty : Option (BitVec 32)
  limitOrderMaxFloorQty : Option (BitVec 32)
  limitOrderMaxReplenishQtyRange : Option (BitVec 32)
  limitOrderMaxReplenishTimeRange : Option (BitVec 64)
  limitOrderReferencePriceTarget : Option (BitVec 16)
  limitOrderExpireTime : Option (BitVec 64)
  limitOrderUserData : Option (BitVec 64)
  limitOrderMpid : Option (Alpha 4)
  limitOrderMemberGroup : Option (Alpha 2)
  limitOrderLocateBroker : Option (Alpha 4)
  deriving DecidableEq, Repr

namespace LimitOrderMessage

def encode (message : LimitOrderMessage) : List UInt8 :=
  encodeUIntLE 4 (message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome)
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.limitOrderBitFields
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeOptional (encodeUIntLE 1) message.limitOrderSelfMatchScope
    ++ (encodeOptional (encodeUIntLE 1) message.limitOrderSelfMatchInstruction
    ++ (encodeOptional (encodeUIntLE 1) message.limitOrderPriceSlideInstruction
    ++ (encodeOptional (encodeUIntLE 4) message.limitOrderMinQty
    ++ (encodeOptional (encodeUIntLE 4) message.limitOrderMaxFloorQty
    ++ (encodeOptional (encodeUIntLE 4) message.limitOrderMaxReplenishQtyRange
    ++ (encodeOptional (encodeUIntLE 8) message.limitOrderMaxReplenishTimeRange
    ++ (encodeOptional (encodeUIntLE 2) message.limitOrderReferencePriceTarget
    ++ (encodeOptional (encodeUIntLE 8) message.limitOrderExpireTime
    ++ (encodeOptional (encodeUIntLE 8) message.limitOrderUserData
    ++ (encodeOptional (Alpha.encode) message.limitOrderMpid
    ++ (encodeOptional (Alpha.encode) message.limitOrderMemberGroup
    ++ (encodeOptional (Alpha.encode) message.limitOrderLocateBroker))))))))))))))))))

def decode (bytes : List UInt8) : Option (LimitOrderMessage × List UInt8) := do
  let (limitOrderPresenceBits_, bytes) ← decodeUIntLE 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (limitOrderBitFields, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (limitOrderSelfMatchScope, bytes) ← decodeOptional (decodeUIntLE 1) (limitOrderPresenceBits_ &&& 1 != 0) bytes
  let (limitOrderSelfMatchInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (limitOrderPresenceBits_ &&& 2 != 0) bytes
  let (limitOrderPriceSlideInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (limitOrderPresenceBits_ &&& 4 != 0) bytes
  let (limitOrderMinQty, bytes) ← decodeOptional (decodeUIntLE 4) (limitOrderPresenceBits_ &&& 8 != 0) bytes
  let (limitOrderMaxFloorQty, bytes) ← decodeOptional (decodeUIntLE 4) (limitOrderPresenceBits_ &&& 16 != 0) bytes
  let (limitOrderMaxReplenishQtyRange, bytes) ← decodeOptional (decodeUIntLE 4) (limitOrderPresenceBits_ &&& 32 != 0) bytes
  let (limitOrderMaxReplenishTimeRange, bytes) ← decodeOptional (decodeUIntLE 8) (limitOrderPresenceBits_ &&& 64 != 0) bytes
  let (limitOrderReferencePriceTarget, bytes) ← decodeOptional (decodeUIntLE 2) (limitOrderPresenceBits_ &&& 128 != 0) bytes
  let (limitOrderExpireTime, bytes) ← decodeOptional (decodeUIntLE 8) (limitOrderPresenceBits_ &&& 256 != 0) bytes
  let (limitOrderUserData, bytes) ← decodeOptional (decodeUIntLE 8) (limitOrderPresenceBits_ &&& 512 != 0) bytes
  let (limitOrderMpid, bytes) ← decodeOptional (Alpha.decode 4) (limitOrderPresenceBits_ &&& 1024 != 0) bytes
  let (limitOrderMemberGroup, bytes) ← decodeOptional (Alpha.decode 2) (limitOrderPresenceBits_ &&& 2048 != 0) bytes
  let (limitOrderLocateBroker, bytes) ← decodeOptional (Alpha.decode 4) (limitOrderPresenceBits_ &&& 4096 != 0) bytes
  if fits_limitOrderPresenceBits : (limitOrderPresenceBits_ &&& 4294959104) &&& 8191 = 0 then
    pure ({ limitOrderPresenceBits := ⟨limitOrderPresenceBits_ &&& 4294959104, fits_limitOrderPresenceBits⟩, clOrdId, orderQty, limitOrderBitFields, symbolId, price, limitOrderSelfMatchScope, limitOrderSelfMatchInstruction, limitOrderPriceSlideInstruction, limitOrderMinQty, limitOrderMaxFloorQty, limitOrderMaxReplenishQtyRange, limitOrderMaxReplenishTimeRange, limitOrderReferencePriceTarget, limitOrderExpireTime, limitOrderUserData, limitOrderMpid, limitOrderMemberGroup, limitOrderLocateBroker }, bytes)
  else none

theorem encode_length_pos (message : LimitOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : LimitOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_limitOrderSelfMatchScope : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 1 != 0) = message.limitOrderSelfMatchScope.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderSelfMatchInstruction : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 2 != 0) = message.limitOrderSelfMatchInstruction.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderPriceSlideInstruction : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 4 != 0) = message.limitOrderPriceSlideInstruction.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderMinQty : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 8 != 0) = message.limitOrderMinQty.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderMaxFloorQty : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 16 != 0) = message.limitOrderMaxFloorQty.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderMaxReplenishQtyRange : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 32 != 0) = message.limitOrderMaxReplenishQtyRange.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderMaxReplenishTimeRange : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 64 != 0) = message.limitOrderMaxReplenishTimeRange.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderReferencePriceTarget : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 128 != 0) = message.limitOrderReferencePriceTarget.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderExpireTime : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 256 != 0) = message.limitOrderExpireTime.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderUserData : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 512 != 0) = message.limitOrderUserData.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderMpid : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 1024 != 0) = message.limitOrderMpid.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderMemberGroup : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 2048 != 0) = message.limitOrderMemberGroup.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderLocateBroker : ((message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 4096 != 0) = message.limitOrderLocateBroker.isSome := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_limitOrderPresenceBits : (message.limitOrderPresenceBits.val ||| presence (n := 32) 1 message.limitOrderSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderMinQty.isSome ||| presence (n := 32) 16 message.limitOrderMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderUserData.isSome ||| presence (n := 32) 1024 message.limitOrderMpid.isSome ||| presence (n := 32) 2048 message.limitOrderMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderLocateBroker.isSome) &&& 4294959104 = message.limitOrderPresenceBits.val := by
    have clear := message.limitOrderPresenceBits.property
    simp only [presence]
    bv_decide
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_limitOrderSelfMatchScope]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_limitOrderSelfMatchInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_limitOrderPriceSlideInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_limitOrderMinQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_limitOrderMaxFloorQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_limitOrderMaxReplenishQtyRange]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_limitOrderMaxReplenishTimeRange]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_limitOrderReferencePriceTarget]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 2) (decodeUIntLE 2) (decodeUIntLE_encodeUIntLE 2), some_bind]
  dsimp only
  rw [selected_limitOrderExpireTime]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_limitOrderUserData]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_limitOrderMpid]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_limitOrderMemberGroup]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 2) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_limitOrderLocateBroker]
  rw [decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_limitOrderPresenceBits]; exact message.limitOrderPresenceBits.property)]
  simp only [carried_limitOrderPresenceBits]
  rfl

end LimitOrderMessage

/-- Market Order Message -/
structure MarketOrderMessage where
  marketOrderPresenceBits : Masked 16 63
  clOrdId : BitVec 64
  orderQty : BitVec 32
  marketOrderBitFields : BitVec 16
  symbolId : BitVec 16
  marketOrderSelfMatchScope : Option (BitVec 8)
  marketOrderSelfMatchInstruction : Option (BitVec 8)
  marketOrderUserData : Option (BitVec 64)
  marketOrderMpid : Option (Alpha 4)
  marketOrderMemberGroup : Option (Alpha 2)
  marketOrderLocateBroker : Option (Alpha 4)
  deriving DecidableEq, Repr

namespace MarketOrderMessage

def encode (message : MarketOrderMessage) : List UInt8 :=
  encodeUIntLE 2 (message.marketOrderPresenceBits.val ||| presence (n := 16) 1 message.marketOrderSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderUserData.isSome ||| presence (n := 16) 8 message.marketOrderMpid.isSome ||| presence (n := 16) 16 message.marketOrderMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderLocateBroker.isSome)
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 2 message.marketOrderBitFields
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeOptional (encodeUIntLE 1) message.marketOrderSelfMatchScope
    ++ (encodeOptional (encodeUIntLE 1) message.marketOrderSelfMatchInstruction
    ++ (encodeOptional (encodeUIntLE 8) message.marketOrderUserData
    ++ (encodeOptional (Alpha.encode) message.marketOrderMpid
    ++ (encodeOptional (Alpha.encode) message.marketOrderMemberGroup
    ++ (encodeOptional (Alpha.encode) message.marketOrderLocateBroker))))))))))

def decode (bytes : List UInt8) : Option (MarketOrderMessage × List UInt8) := do
  let (marketOrderPresenceBits_, bytes) ← decodeUIntLE 2 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (marketOrderBitFields, bytes) ← decodeUIntLE 2 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (marketOrderSelfMatchScope, bytes) ← decodeOptional (decodeUIntLE 1) (marketOrderPresenceBits_ &&& 1 != 0) bytes
  let (marketOrderSelfMatchInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (marketOrderPresenceBits_ &&& 2 != 0) bytes
  let (marketOrderUserData, bytes) ← decodeOptional (decodeUIntLE 8) (marketOrderPresenceBits_ &&& 4 != 0) bytes
  let (marketOrderMpid, bytes) ← decodeOptional (Alpha.decode 4) (marketOrderPresenceBits_ &&& 8 != 0) bytes
  let (marketOrderMemberGroup, bytes) ← decodeOptional (Alpha.decode 2) (marketOrderPresenceBits_ &&& 16 != 0) bytes
  let (marketOrderLocateBroker, bytes) ← decodeOptional (Alpha.decode 4) (marketOrderPresenceBits_ &&& 32 != 0) bytes
  if fits_marketOrderPresenceBits : (marketOrderPresenceBits_ &&& 65472) &&& 63 = 0 then
    pure ({ marketOrderPresenceBits := ⟨marketOrderPresenceBits_ &&& 65472, fits_marketOrderPresenceBits⟩, clOrdId, orderQty, marketOrderBitFields, symbolId, marketOrderSelfMatchScope, marketOrderSelfMatchInstruction, marketOrderUserData, marketOrderMpid, marketOrderMemberGroup, marketOrderLocateBroker }, bytes)
  else none

theorem encode_length_pos (message : MarketOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : MarketOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_marketOrderSelfMatchScope : ((message.marketOrderPresenceBits.val ||| presence (n := 16) 1 message.marketOrderSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderUserData.isSome ||| presence (n := 16) 8 message.marketOrderMpid.isSome ||| presence (n := 16) 16 message.marketOrderMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderLocateBroker.isSome) &&& 1 != 0) = message.marketOrderSelfMatchScope.isSome := by
    have clear := message.marketOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderSelfMatchInstruction : ((message.marketOrderPresenceBits.val ||| presence (n := 16) 1 message.marketOrderSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderUserData.isSome ||| presence (n := 16) 8 message.marketOrderMpid.isSome ||| presence (n := 16) 16 message.marketOrderMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderLocateBroker.isSome) &&& 2 != 0) = message.marketOrderSelfMatchInstruction.isSome := by
    have clear := message.marketOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderUserData : ((message.marketOrderPresenceBits.val ||| presence (n := 16) 1 message.marketOrderSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderUserData.isSome ||| presence (n := 16) 8 message.marketOrderMpid.isSome ||| presence (n := 16) 16 message.marketOrderMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderLocateBroker.isSome) &&& 4 != 0) = message.marketOrderUserData.isSome := by
    have clear := message.marketOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderMpid : ((message.marketOrderPresenceBits.val ||| presence (n := 16) 1 message.marketOrderSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderUserData.isSome ||| presence (n := 16) 8 message.marketOrderMpid.isSome ||| presence (n := 16) 16 message.marketOrderMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderLocateBroker.isSome) &&& 8 != 0) = message.marketOrderMpid.isSome := by
    have clear := message.marketOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderMemberGroup : ((message.marketOrderPresenceBits.val ||| presence (n := 16) 1 message.marketOrderSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderUserData.isSome ||| presence (n := 16) 8 message.marketOrderMpid.isSome ||| presence (n := 16) 16 message.marketOrderMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderLocateBroker.isSome) &&& 16 != 0) = message.marketOrderMemberGroup.isSome := by
    have clear := message.marketOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderLocateBroker : ((message.marketOrderPresenceBits.val ||| presence (n := 16) 1 message.marketOrderSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderUserData.isSome ||| presence (n := 16) 8 message.marketOrderMpid.isSome ||| presence (n := 16) 16 message.marketOrderMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderLocateBroker.isSome) &&& 32 != 0) = message.marketOrderLocateBroker.isSome := by
    have clear := message.marketOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_marketOrderPresenceBits : (message.marketOrderPresenceBits.val ||| presence (n := 16) 1 message.marketOrderSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderUserData.isSome ||| presence (n := 16) 8 message.marketOrderMpid.isSome ||| presence (n := 16) 16 message.marketOrderMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderLocateBroker.isSome) &&& 65472 = message.marketOrderPresenceBits.val := by
    have clear := message.marketOrderPresenceBits.property
    simp only [presence]
    bv_decide
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_marketOrderSelfMatchScope]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_marketOrderSelfMatchInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_marketOrderUserData]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_marketOrderMpid]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_marketOrderMemberGroup]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 2) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_marketOrderLocateBroker]
  rw [decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_marketOrderPresenceBits]; exact message.marketOrderPresenceBits.property)]
  simp only [carried_marketOrderPresenceBits]
  rfl

end MarketOrderMessage

/-- Cancel Order Message: 8 bytes -/
structure CancelOrderMessage where
  origClOrdId : BitVec 64
  deriving DecidableEq, Repr

namespace CancelOrderMessage

def encode (message : CancelOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.origClOrdId

def decode (bytes : List UInt8) : Option (CancelOrderMessage × List UInt8) := do
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  pure ({ origClOrdId }, bytes)

@[simp] theorem encode_length (message : CancelOrderMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : CancelOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CancelOrderMessage

/-- Modify Order Message -/
structure ModifyOrderMessage where
  modifyOrderPresenceBits : Masked 8 7
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  modifyOrderOrderQty : Option (BitVec 32)
  modifyOrderBitFields : Option (BitVec 8)
  modifyOrderLocateBroker : Option (Alpha 4)
  deriving DecidableEq, Repr

namespace ModifyOrderMessage

def encode (message : ModifyOrderMessage) : List UInt8 :=
  encodeUIntLE 1 (message.modifyOrderPresenceBits.val ||| presence (n := 8) 1 message.modifyOrderOrderQty.isSome ||| presence (n := 8) 2 message.modifyOrderBitFields.isSome ||| presence (n := 8) 4 message.modifyOrderLocateBroker.isSome)
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeOptional (encodeUIntLE 4) message.modifyOrderOrderQty
    ++ (encodeOptional (encodeUIntLE 1) message.modifyOrderBitFields
    ++ (encodeOptional (Alpha.encode) message.modifyOrderLocateBroker)))))

def decode (bytes : List UInt8) : Option (ModifyOrderMessage × List UInt8) := do
  let (modifyOrderPresenceBits_, bytes) ← decodeUIntLE 1 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (modifyOrderOrderQty, bytes) ← decodeOptional (decodeUIntLE 4) (modifyOrderPresenceBits_ &&& 1 != 0) bytes
  let (modifyOrderBitFields, bytes) ← decodeOptional (decodeUIntLE 1) (modifyOrderPresenceBits_ &&& 2 != 0) bytes
  let (modifyOrderLocateBroker, bytes) ← decodeOptional (Alpha.decode 4) (modifyOrderPresenceBits_ &&& 4 != 0) bytes
  if fits_modifyOrderPresenceBits : (modifyOrderPresenceBits_ &&& 248) &&& 7 = 0 then
    pure ({ modifyOrderPresenceBits := ⟨modifyOrderPresenceBits_ &&& 248, fits_modifyOrderPresenceBits⟩, clOrdId, origClOrdId, modifyOrderOrderQty, modifyOrderBitFields, modifyOrderLocateBroker }, bytes)
  else none

theorem encode_length_pos (message : ModifyOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : ModifyOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_modifyOrderOrderQty : ((message.modifyOrderPresenceBits.val ||| presence (n := 8) 1 message.modifyOrderOrderQty.isSome ||| presence (n := 8) 2 message.modifyOrderBitFields.isSome ||| presence (n := 8) 4 message.modifyOrderLocateBroker.isSome) &&& 1 != 0) = message.modifyOrderOrderQty.isSome := by
    have clear := message.modifyOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_modifyOrderBitFields : ((message.modifyOrderPresenceBits.val ||| presence (n := 8) 1 message.modifyOrderOrderQty.isSome ||| presence (n := 8) 2 message.modifyOrderBitFields.isSome ||| presence (n := 8) 4 message.modifyOrderLocateBroker.isSome) &&& 2 != 0) = message.modifyOrderBitFields.isSome := by
    have clear := message.modifyOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_modifyOrderLocateBroker : ((message.modifyOrderPresenceBits.val ||| presence (n := 8) 1 message.modifyOrderOrderQty.isSome ||| presence (n := 8) 2 message.modifyOrderBitFields.isSome ||| presence (n := 8) 4 message.modifyOrderLocateBroker.isSome) &&& 4 != 0) = message.modifyOrderLocateBroker.isSome := by
    have clear := message.modifyOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_modifyOrderPresenceBits : (message.modifyOrderPresenceBits.val ||| presence (n := 8) 1 message.modifyOrderOrderQty.isSome ||| presence (n := 8) 2 message.modifyOrderBitFields.isSome ||| presence (n := 8) 4 message.modifyOrderLocateBroker.isSome) &&& 248 = message.modifyOrderPresenceBits.val := by
    have clear := message.modifyOrderPresenceBits.property
    simp only [presence]
    bv_decide
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_modifyOrderOrderQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_modifyOrderBitFields]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_modifyOrderLocateBroker]
  rw [decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_modifyOrderPresenceBits]; exact message.modifyOrderPresenceBits.property)]
  simp only [carried_modifyOrderPresenceBits]
  rfl

end ModifyOrderMessage

/-- Replace Order Message -/
structure ReplaceOrderMessage where
  replaceOrderPresenceBits : Masked 16 255
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  replaceOrderBitFields : BitVec 16
  replaceOrderPrice : Option (BitVec 64)
  replaceOrderOrderQty : Option (BitVec 32)
  replaceOrderMaxFloorQty : Option (BitVec 32)
  replaceOrderSelfMatchScope : Option (BitVec 8)
  replaceOrderSelfMatchInstruction : Option (BitVec 8)
  replaceOrderPriceSlideInstruction : Option (BitVec 8)
  replaceOrderReferencePriceTarget : Option (BitVec 16)
  replaceOrderLocateBroker : Option (Alpha 4)
  deriving DecidableEq, Repr

namespace ReplaceOrderMessage

def encode (message : ReplaceOrderMessage) : List UInt8 :=
  encodeUIntLE 2 (message.replaceOrderPresenceBits.val ||| presence (n := 16) 1 message.replaceOrderPrice.isSome ||| presence (n := 16) 2 message.replaceOrderOrderQty.isSome ||| presence (n := 16) 4 message.replaceOrderMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceOrderSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceOrderSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceOrderPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceOrderReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceOrderLocateBroker.isSome)
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 2 message.replaceOrderBitFields
    ++ (encodeOptional (encodeUIntLE 8) message.replaceOrderPrice
    ++ (encodeOptional (encodeUIntLE 4) message.replaceOrderOrderQty
    ++ (encodeOptional (encodeUIntLE 4) message.replaceOrderMaxFloorQty
    ++ (encodeOptional (encodeUIntLE 1) message.replaceOrderSelfMatchScope
    ++ (encodeOptional (encodeUIntLE 1) message.replaceOrderSelfMatchInstruction
    ++ (encodeOptional (encodeUIntLE 1) message.replaceOrderPriceSlideInstruction
    ++ (encodeOptional (encodeUIntLE 2) message.replaceOrderReferencePriceTarget
    ++ (encodeOptional (Alpha.encode) message.replaceOrderLocateBroker)))))))))))

def decode (bytes : List UInt8) : Option (ReplaceOrderMessage × List UInt8) := do
  let (replaceOrderPresenceBits_, bytes) ← decodeUIntLE 2 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (replaceOrderBitFields, bytes) ← decodeUIntLE 2 bytes
  let (replaceOrderPrice, bytes) ← decodeOptional (decodeUIntLE 8) (replaceOrderPresenceBits_ &&& 1 != 0) bytes
  let (replaceOrderOrderQty, bytes) ← decodeOptional (decodeUIntLE 4) (replaceOrderPresenceBits_ &&& 2 != 0) bytes
  let (replaceOrderMaxFloorQty, bytes) ← decodeOptional (decodeUIntLE 4) (replaceOrderPresenceBits_ &&& 4 != 0) bytes
  let (replaceOrderSelfMatchScope, bytes) ← decodeOptional (decodeUIntLE 1) (replaceOrderPresenceBits_ &&& 8 != 0) bytes
  let (replaceOrderSelfMatchInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (replaceOrderPresenceBits_ &&& 16 != 0) bytes
  let (replaceOrderPriceSlideInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (replaceOrderPresenceBits_ &&& 32 != 0) bytes
  let (replaceOrderReferencePriceTarget, bytes) ← decodeOptional (decodeUIntLE 2) (replaceOrderPresenceBits_ &&& 64 != 0) bytes
  let (replaceOrderLocateBroker, bytes) ← decodeOptional (Alpha.decode 4) (replaceOrderPresenceBits_ &&& 128 != 0) bytes
  if fits_replaceOrderPresenceBits : (replaceOrderPresenceBits_ &&& 65280) &&& 255 = 0 then
    pure ({ replaceOrderPresenceBits := ⟨replaceOrderPresenceBits_ &&& 65280, fits_replaceOrderPresenceBits⟩, clOrdId, origClOrdId, replaceOrderBitFields, replaceOrderPrice, replaceOrderOrderQty, replaceOrderMaxFloorQty, replaceOrderSelfMatchScope, replaceOrderSelfMatchInstruction, replaceOrderPriceSlideInstruction, replaceOrderReferencePriceTarget, replaceOrderLocateBroker }, bytes)
  else none

theorem encode_length_pos (message : ReplaceOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : ReplaceOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_replaceOrderPrice : ((message.replaceOrderPresenceBits.val ||| presence (n := 16) 1 message.replaceOrderPrice.isSome ||| presence (n := 16) 2 message.replaceOrderOrderQty.isSome ||| presence (n := 16) 4 message.replaceOrderMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceOrderSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceOrderSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceOrderPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceOrderReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceOrderLocateBroker.isSome) &&& 1 != 0) = message.replaceOrderPrice.isSome := by
    have clear := message.replaceOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceOrderOrderQty : ((message.replaceOrderPresenceBits.val ||| presence (n := 16) 1 message.replaceOrderPrice.isSome ||| presence (n := 16) 2 message.replaceOrderOrderQty.isSome ||| presence (n := 16) 4 message.replaceOrderMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceOrderSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceOrderSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceOrderPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceOrderReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceOrderLocateBroker.isSome) &&& 2 != 0) = message.replaceOrderOrderQty.isSome := by
    have clear := message.replaceOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceOrderMaxFloorQty : ((message.replaceOrderPresenceBits.val ||| presence (n := 16) 1 message.replaceOrderPrice.isSome ||| presence (n := 16) 2 message.replaceOrderOrderQty.isSome ||| presence (n := 16) 4 message.replaceOrderMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceOrderSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceOrderSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceOrderPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceOrderReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceOrderLocateBroker.isSome) &&& 4 != 0) = message.replaceOrderMaxFloorQty.isSome := by
    have clear := message.replaceOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceOrderSelfMatchScope : ((message.replaceOrderPresenceBits.val ||| presence (n := 16) 1 message.replaceOrderPrice.isSome ||| presence (n := 16) 2 message.replaceOrderOrderQty.isSome ||| presence (n := 16) 4 message.replaceOrderMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceOrderSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceOrderSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceOrderPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceOrderReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceOrderLocateBroker.isSome) &&& 8 != 0) = message.replaceOrderSelfMatchScope.isSome := by
    have clear := message.replaceOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceOrderSelfMatchInstruction : ((message.replaceOrderPresenceBits.val ||| presence (n := 16) 1 message.replaceOrderPrice.isSome ||| presence (n := 16) 2 message.replaceOrderOrderQty.isSome ||| presence (n := 16) 4 message.replaceOrderMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceOrderSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceOrderSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceOrderPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceOrderReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceOrderLocateBroker.isSome) &&& 16 != 0) = message.replaceOrderSelfMatchInstruction.isSome := by
    have clear := message.replaceOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceOrderPriceSlideInstruction : ((message.replaceOrderPresenceBits.val ||| presence (n := 16) 1 message.replaceOrderPrice.isSome ||| presence (n := 16) 2 message.replaceOrderOrderQty.isSome ||| presence (n := 16) 4 message.replaceOrderMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceOrderSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceOrderSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceOrderPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceOrderReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceOrderLocateBroker.isSome) &&& 32 != 0) = message.replaceOrderPriceSlideInstruction.isSome := by
    have clear := message.replaceOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceOrderReferencePriceTarget : ((message.replaceOrderPresenceBits.val ||| presence (n := 16) 1 message.replaceOrderPrice.isSome ||| presence (n := 16) 2 message.replaceOrderOrderQty.isSome ||| presence (n := 16) 4 message.replaceOrderMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceOrderSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceOrderSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceOrderPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceOrderReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceOrderLocateBroker.isSome) &&& 64 != 0) = message.replaceOrderReferencePriceTarget.isSome := by
    have clear := message.replaceOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceOrderLocateBroker : ((message.replaceOrderPresenceBits.val ||| presence (n := 16) 1 message.replaceOrderPrice.isSome ||| presence (n := 16) 2 message.replaceOrderOrderQty.isSome ||| presence (n := 16) 4 message.replaceOrderMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceOrderSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceOrderSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceOrderPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceOrderReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceOrderLocateBroker.isSome) &&& 128 != 0) = message.replaceOrderLocateBroker.isSome := by
    have clear := message.replaceOrderPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_replaceOrderPresenceBits : (message.replaceOrderPresenceBits.val ||| presence (n := 16) 1 message.replaceOrderPrice.isSome ||| presence (n := 16) 2 message.replaceOrderOrderQty.isSome ||| presence (n := 16) 4 message.replaceOrderMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceOrderSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceOrderSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceOrderPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceOrderReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceOrderLocateBroker.isSome) &&& 65280 = message.replaceOrderPresenceBits.val := by
    have clear := message.replaceOrderPresenceBits.property
    simp only [presence]
    bv_decide
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_replaceOrderPrice]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_replaceOrderOrderQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_replaceOrderMaxFloorQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_replaceOrderSelfMatchScope]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_replaceOrderSelfMatchInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_replaceOrderPriceSlideInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_replaceOrderReferencePriceTarget]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 2) (decodeUIntLE 2) (decodeUIntLE_encodeUIntLE 2), some_bind]
  dsimp only
  rw [selected_replaceOrderLocateBroker]
  rw [decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_replaceOrderPresenceBits]; exact message.replaceOrderPresenceBits.property)]
  simp only [carried_replaceOrderPresenceBits]
  rfl

end ReplaceOrderMessage

/-- Mass Cancel Message -/
structure MassCancelMessage where
  massCancelPresenceBits : Masked 8 15
  massCancelRequestId : BitVec 64
  massCancelScope : BitVec 8
  massCancelBitFields : BitVec 8
  massCancelMpid : Option (Alpha 4)
  massCancelSenderComp : Option (Alpha 8)
  massCancelMemberGroup : Option (Alpha 2)
  massCancelClOrdId : Option (BitVec 64)
  deriving DecidableEq, Repr

namespace MassCancelMessage

def encode (message : MassCancelMessage) : List UInt8 :=
  encodeUIntLE 1 (message.massCancelPresenceBits.val ||| presence (n := 8) 1 message.massCancelMpid.isSome ||| presence (n := 8) 2 message.massCancelSenderComp.isSome ||| presence (n := 8) 4 message.massCancelMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelClOrdId.isSome)
    ++ (encodeUIntLE 8 message.massCancelRequestId
    ++ (encodeUIntLE 1 message.massCancelScope
    ++ (encodeUIntLE 1 message.massCancelBitFields
    ++ (encodeOptional (Alpha.encode) message.massCancelMpid
    ++ (encodeOptional (Alpha.encode) message.massCancelSenderComp
    ++ (encodeOptional (Alpha.encode) message.massCancelMemberGroup
    ++ (encodeOptional (encodeUIntLE 8) message.massCancelClOrdId)))))))

def decode (bytes : List UInt8) : Option (MassCancelMessage × List UInt8) := do
  let (massCancelPresenceBits_, bytes) ← decodeUIntLE 1 bytes
  let (massCancelRequestId, bytes) ← decodeUIntLE 8 bytes
  let (massCancelScope, bytes) ← decodeUIntLE 1 bytes
  let (massCancelBitFields, bytes) ← decodeUIntLE 1 bytes
  let (massCancelMpid, bytes) ← decodeOptional (Alpha.decode 4) (massCancelPresenceBits_ &&& 1 != 0) bytes
  let (massCancelSenderComp, bytes) ← decodeOptional (Alpha.decode 8) (massCancelPresenceBits_ &&& 2 != 0) bytes
  let (massCancelMemberGroup, bytes) ← decodeOptional (Alpha.decode 2) (massCancelPresenceBits_ &&& 4 != 0) bytes
  let (massCancelClOrdId, bytes) ← decodeOptional (decodeUIntLE 8) (massCancelPresenceBits_ &&& 8 != 0) bytes
  if fits_massCancelPresenceBits : (massCancelPresenceBits_ &&& 240) &&& 15 = 0 then
    pure ({ massCancelPresenceBits := ⟨massCancelPresenceBits_ &&& 240, fits_massCancelPresenceBits⟩, massCancelRequestId, massCancelScope, massCancelBitFields, massCancelMpid, massCancelSenderComp, massCancelMemberGroup, massCancelClOrdId }, bytes)
  else none

theorem encode_length_pos (message : MassCancelMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : MassCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_massCancelMpid : ((message.massCancelPresenceBits.val ||| presence (n := 8) 1 message.massCancelMpid.isSome ||| presence (n := 8) 2 message.massCancelSenderComp.isSome ||| presence (n := 8) 4 message.massCancelMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelClOrdId.isSome) &&& 1 != 0) = message.massCancelMpid.isSome := by
    have clear := message.massCancelPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_massCancelSenderComp : ((message.massCancelPresenceBits.val ||| presence (n := 8) 1 message.massCancelMpid.isSome ||| presence (n := 8) 2 message.massCancelSenderComp.isSome ||| presence (n := 8) 4 message.massCancelMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelClOrdId.isSome) &&& 2 != 0) = message.massCancelSenderComp.isSome := by
    have clear := message.massCancelPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_massCancelMemberGroup : ((message.massCancelPresenceBits.val ||| presence (n := 8) 1 message.massCancelMpid.isSome ||| presence (n := 8) 2 message.massCancelSenderComp.isSome ||| presence (n := 8) 4 message.massCancelMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelClOrdId.isSome) &&& 4 != 0) = message.massCancelMemberGroup.isSome := by
    have clear := message.massCancelPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_massCancelClOrdId : ((message.massCancelPresenceBits.val ||| presence (n := 8) 1 message.massCancelMpid.isSome ||| presence (n := 8) 2 message.massCancelSenderComp.isSome ||| presence (n := 8) 4 message.massCancelMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelClOrdId.isSome) &&& 8 != 0) = message.massCancelClOrdId.isSome := by
    have clear := message.massCancelPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_massCancelPresenceBits : (message.massCancelPresenceBits.val ||| presence (n := 8) 1 message.massCancelMpid.isSome ||| presence (n := 8) 2 message.massCancelSenderComp.isSome ||| presence (n := 8) 4 message.massCancelMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelClOrdId.isSome) &&& 240 = message.massCancelPresenceBits.val := by
    have clear := message.massCancelPresenceBits.property
    simp only [presence]
    bv_decide
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_massCancelMpid]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_massCancelSenderComp]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 8) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_massCancelMemberGroup]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 2) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_massCancelClOrdId]
  rw [decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_massCancelPresenceBits]; exact message.massCancelPresenceBits.property)]
  simp only [carried_massCancelPresenceBits]
  rfl

end MassCancelMessage

/-- Any Unsequenced Message, selected by Message Type -/
inductive UnsequencedMessage where
  | limitOrderMessage (message : LimitOrderMessage) -- 76
  | marketOrderMessage (message : MarketOrderMessage) -- 65
  | cancelOrderMessage (message : CancelOrderMessage) -- 67
  | modifyOrderMessage (message : ModifyOrderMessage) -- 77
  | replaceOrderMessage (message : ReplaceOrderMessage) -- 82
  | massCancelMessage (message : MassCancelMessage) -- 86
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .limitOrderMessage _ => 76
  | .marketOrderMessage _ => 65
  | .cancelOrderMessage _ => 67
  | .modifyOrderMessage _ => 77
  | .replaceOrderMessage _ => 82
  | .massCancelMessage _ => 86

def encode : UnsequencedMessage → List UInt8
  | .limitOrderMessage message => LimitOrderMessage.encode message
  | .marketOrderMessage message => MarketOrderMessage.encode message
  | .cancelOrderMessage message => CancelOrderMessage.encode message
  | .modifyOrderMessage message => ModifyOrderMessage.encode message
  | .replaceOrderMessage message => ReplaceOrderMessage.encode message
  | .massCancelMessage message => MassCancelMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 76 then (LimitOrderMessage.decode bytes).map fun (message, rest) => (.limitOrderMessage message, rest)
  else if tag = 65 then (MarketOrderMessage.decode bytes).map fun (message, rest) => (.marketOrderMessage message, rest)
  else if tag = 67 then (CancelOrderMessage.decode bytes).map fun (message, rest) => (.cancelOrderMessage message, rest)
  else if tag = 77 then (ModifyOrderMessage.decode bytes).map fun (message, rest) => (.modifyOrderMessage message, rest)
  else if tag = 82 then (ReplaceOrderMessage.decode bytes).map fun (message, rest) => (.replaceOrderMessage message, rest)
  else if tag = 86 then (MassCancelMessage.decode bytes).map fun (message, rest) => (.massCancelMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Tcp Unsequenced Message -/
structure TcpUnsequencedMessage where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace TcpUnsequencedMessage

def encode (message : TcpUnsequencedMessage) : List UInt8 :=
  encodeUInt 1 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (TcpUnsequencedMessage × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode messageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : TcpUnsequencedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : TcpUnsequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

end TcpUnsequencedMessage

/-- Any Client Payload, selected by Packet Type -/
inductive ClientPayload where
  | logonRequestPacket (message : LogonRequestPacket) -- 53
  | tcpUnsequencedMessage (message : TcpUnsequencedMessage) -- 54
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .logonRequestPacket _ => 53
  | .tcpUnsequencedMessage _ => 54

def encode : ClientPayload → List UInt8
  | .logonRequestPacket message => LogonRequestPacket.encode message
  | .tcpUnsequencedMessage message => TcpUnsequencedMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 53 then (LogonRequestPacket.decode bytes).map fun (message, rest) => (.logonRequestPacket message, rest)
  else if tag = 54 then (TcpUnsequencedMessage.decode bytes).map fun (message, rest) => (.tcpUnsequencedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Rake Tcp Message -/
structure ClientRakeTcpMessage where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientRakeTcpMessage

def encodeBody (message : ClientRakeTcpMessage) : List UInt8 :=
  encodeUIntLE 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option (ClientRakeTcpMessage × List UInt8) := do
  let (packetType, bytes) ← decodeUIntLE 1 bytes
  let (clientPayload, bytes) ← ClientPayload.decode packetType bytes
  pure ({ clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientRakeTcpMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

/-- Size rule: Message Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ClientRakeTcpMessage) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (ClientRakeTcpMessage × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ClientRakeTcpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ClientRakeTcpMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end ClientRakeTcpMessage

/-- Client Packet -/
structure ClientPacket where
  clientRakeTcpMessage : List ClientRakeTcpMessage
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientRakeTcpMessage.encode message.clientRakeTcpMessage

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientRakeTcpMessage ← decodeAll ClientRakeTcpMessage.decode bytes.length bytes
  pure { clientRakeTcpMessage }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientRakeTcpMessage.encode ClientRakeTcpMessage.decode ClientRakeTcpMessage.decode_encode ClientRakeTcpMessage.encode_length_pos message.clientRakeTcpMessage _ (encodeMany_length_ge ClientRakeTcpMessage.encode ClientRakeTcpMessage.encode_length_pos message.clientRakeTcpMessage), some_bind]
  rfl

end ClientPacket

end Omi.TxseTxseequitiesSeedRakeV10Client
