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

namespace Omi.TxseTxseequitiesSeedRakeV10

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogonRequestPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TcpUnsequencedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TcpUnsequencedMessage

/-- Debug Message -/
structure DebugMessage where
  text : Capped 65479
  deriving DecidableEq, Repr

namespace DebugMessage

def encode (message : DebugMessage) : List UInt8 :=
  message.text.val

def decode (bytes : List UInt8) : Option DebugMessage := do
  let text_ := bytes
  if fits_text : text_.length ≤ 65479 then
    pure { text := ⟨text_, fits_text⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugMessage) : (encode message).length ≤ 65479 := by
  have bound_text := message.text.length_le
  unfold encode
  omega

theorem decode_encode (message : DebugMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.text.length_le]
  rfl

end DebugMessage

/-- End Of Session Message: 0 bytes -/
structure EndOfSessionMessage where
  deriving DecidableEq, Repr

namespace EndOfSessionMessage

def encode (_ : EndOfSessionMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSessionMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSessionMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSessionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfSessionMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EndOfSessionMessage

/-- Logon Response Message: 30 bytes -/
structure LogonResponseMessage where
  session : BitVec 64
  nextSequenceNumber : BitVec 64
  highestKnownSequenceNumber : BitVec 64
  logonResponseCode : BitVec 8
  numberStreamIds : BitVec 8
  instance_ : BitVec 32
  deriving DecidableEq, Repr

namespace LogonResponseMessage

def encode (message : LogonResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.session
    ++ (encodeUIntLE 8 message.nextSequenceNumber
    ++ (encodeUIntLE 8 message.highestKnownSequenceNumber
    ++ (encodeUInt 1 message.logonResponseCode
    ++ (encodeUInt 1 message.numberStreamIds
    ++ (encodeUIntLE 4 message.instance_)))))

def decode (bytes : List UInt8) : Option (LogonResponseMessage × List UInt8) := do
  let (session, bytes) ← decodeUIntLE 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (highestKnownSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (logonResponseCode, bytes) ← decodeUInt 1 bytes
  let (numberStreamIds, bytes) ← decodeUInt 1 bytes
  let (instance_, bytes) ← decodeUIntLE 4 bytes
  pure ({ session, nextSequenceNumber, highestKnownSequenceNumber, logonResponseCode, numberStreamIds, instance_ }, bytes)

@[simp] theorem encode_length (message : LogonResponseMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LogonResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogonResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LogonResponseMessage

/-- Trading Session Status Message -/
structure TradingSessionStatusMessage where
  tradingSessionStatusPresenceBits : Masked 8 3
  transactTime : BitVec 64
  marketHoursState : BitVec 8
  sessionTradingState : BitVec 8
  tradingSessionStatusOperationalHaltReason : Option (BitVec 8)
  tradingSessionStatusRegulatoryHaltReason : Option (BitVec 8)
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  encodeUIntLE 1 (message.tradingSessionStatusPresenceBits.val ||| presence (n := 8) 1 message.tradingSessionStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.tradingSessionStatusRegulatoryHaltReason.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.marketHoursState
    ++ (encodeUIntLE 1 message.sessionTradingState
    ++ (encodeOptional (encodeUIntLE 1) message.tradingSessionStatusOperationalHaltReason
    ++ (encodeOptional (encodeUIntLE 1) message.tradingSessionStatusRegulatoryHaltReason)))))

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (tradingSessionStatusPresenceBits_, bytes) ← decodeUIntLE 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (marketHoursState, bytes) ← decodeUIntLE 1 bytes
  let (sessionTradingState, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionStatusOperationalHaltReason, bytes) ← decodeOptional (decodeUIntLE 1) (tradingSessionStatusPresenceBits_ &&& 1 != 0) bytes
  let (tradingSessionStatusRegulatoryHaltReason, bytes) ← decodeOptional (decodeUIntLE 1) (tradingSessionStatusPresenceBits_ &&& 2 != 0) bytes
  if fits_tradingSessionStatusPresenceBits : (tradingSessionStatusPresenceBits_ &&& 252) &&& 3 = 0 then
    pure ({ tradingSessionStatusPresenceBits := ⟨tradingSessionStatusPresenceBits_ &&& 252, fits_tradingSessionStatusPresenceBits⟩, transactTime, marketHoursState, sessionTradingState, tradingSessionStatusOperationalHaltReason, tradingSessionStatusRegulatoryHaltReason }, bytes)
  else none

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_tradingSessionStatusOperationalHaltReason : ((message.tradingSessionStatusPresenceBits.val ||| presence (n := 8) 1 message.tradingSessionStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.tradingSessionStatusRegulatoryHaltReason.isSome) &&& 1 != 0) = message.tradingSessionStatusOperationalHaltReason.isSome := by
    have clear := message.tradingSessionStatusPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_tradingSessionStatusRegulatoryHaltReason : ((message.tradingSessionStatusPresenceBits.val ||| presence (n := 8) 1 message.tradingSessionStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.tradingSessionStatusRegulatoryHaltReason.isSome) &&& 2 != 0) = message.tradingSessionStatusRegulatoryHaltReason.isSome := by
    have clear := message.tradingSessionStatusPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_tradingSessionStatusPresenceBits : (message.tradingSessionStatusPresenceBits.val ||| presence (n := 8) 1 message.tradingSessionStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.tradingSessionStatusRegulatoryHaltReason.isSome) &&& 252 = message.tradingSessionStatusPresenceBits.val := by
    have clear := message.tradingSessionStatusPresenceBits.property
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
  rw [selected_tradingSessionStatusOperationalHaltReason]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_tradingSessionStatusRegulatoryHaltReason]
  rw [decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_tradingSessionStatusPresenceBits]; exact message.tradingSessionStatusPresenceBits.property)]
  simp only [carried_tradingSessionStatusPresenceBits]
  rfl

end TradingSessionStatusMessage

/-- Define Symbol Message: 33 bytes -/
structure DefineSymbolMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  symbol : Alpha 8
  suffix : Alpha 8
  matchingEngineId : BitVec 8
  defineSymbolBitFields : BitVec 8
  lotSize : BitVec 32
  listingMarket : BitVec 8
  deriving DecidableEq, Repr

namespace DefineSymbolMessage

def encode (message : DefineSymbolMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.suffix
    ++ (encodeUIntLE 1 message.matchingEngineId
    ++ (encodeUIntLE 1 message.defineSymbolBitFields
    ++ (encodeUIntLE 4 message.lotSize
    ++ (encodeUIntLE 1 message.listingMarket)))))))

def decode (bytes : List UInt8) : Option (DefineSymbolMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (suffix, bytes) ← Alpha.decode 8 bytes
  let (matchingEngineId, bytes) ← decodeUIntLE 1 bytes
  let (defineSymbolBitFields, bytes) ← decodeUIntLE 1 bytes
  let (lotSize, bytes) ← decodeUIntLE 4 bytes
  let (listingMarket, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, symbolId, symbol, suffix, matchingEngineId, defineSymbolBitFields, lotSize, listingMarket }, bytes)

@[simp] theorem encode_length (message : DefineSymbolMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : DefineSymbolMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DefineSymbolMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DefineSymbolMessage

/-- Symbol Status Message -/
structure SymbolStatusMessage where
  symbolStatusPresenceBits : Masked 8 3
  transactTime : BitVec 64
  symbolId : BitVec 16
  symbolTradingState : BitVec 8
  shortSaleRestrictionState : BitVec 8
  symbolStatusOperationalHaltReason : Option (BitVec 8)
  symbolStatusRegulatoryHaltReason : Option (BitVec 8)
  deriving DecidableEq, Repr

namespace SymbolStatusMessage

def encode (message : SymbolStatusMessage) : List UInt8 :=
  encodeUIntLE 1 (message.symbolStatusPresenceBits.val ||| presence (n := 8) 1 message.symbolStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.symbolStatusRegulatoryHaltReason.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 1 message.symbolTradingState
    ++ (encodeUIntLE 1 message.shortSaleRestrictionState
    ++ (encodeOptional (encodeUIntLE 1) message.symbolStatusOperationalHaltReason
    ++ (encodeOptional (encodeUIntLE 1) message.symbolStatusRegulatoryHaltReason))))))

def decode (bytes : List UInt8) : Option (SymbolStatusMessage × List UInt8) := do
  let (symbolStatusPresenceBits_, bytes) ← decodeUIntLE 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (symbolTradingState, bytes) ← decodeUIntLE 1 bytes
  let (shortSaleRestrictionState, bytes) ← decodeUIntLE 1 bytes
  let (symbolStatusOperationalHaltReason, bytes) ← decodeOptional (decodeUIntLE 1) (symbolStatusPresenceBits_ &&& 1 != 0) bytes
  let (symbolStatusRegulatoryHaltReason, bytes) ← decodeOptional (decodeUIntLE 1) (symbolStatusPresenceBits_ &&& 2 != 0) bytes
  if fits_symbolStatusPresenceBits : (symbolStatusPresenceBits_ &&& 252) &&& 3 = 0 then
    pure ({ symbolStatusPresenceBits := ⟨symbolStatusPresenceBits_ &&& 252, fits_symbolStatusPresenceBits⟩, transactTime, symbolId, symbolTradingState, shortSaleRestrictionState, symbolStatusOperationalHaltReason, symbolStatusRegulatoryHaltReason }, bytes)
  else none

theorem encode_length_pos (message : SymbolStatusMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : SymbolStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_symbolStatusOperationalHaltReason : ((message.symbolStatusPresenceBits.val ||| presence (n := 8) 1 message.symbolStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.symbolStatusRegulatoryHaltReason.isSome) &&& 1 != 0) = message.symbolStatusOperationalHaltReason.isSome := by
    have clear := message.symbolStatusPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_symbolStatusRegulatoryHaltReason : ((message.symbolStatusPresenceBits.val ||| presence (n := 8) 1 message.symbolStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.symbolStatusRegulatoryHaltReason.isSome) &&& 2 != 0) = message.symbolStatusRegulatoryHaltReason.isSome := by
    have clear := message.symbolStatusPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_symbolStatusPresenceBits : (message.symbolStatusPresenceBits.val ||| presence (n := 8) 1 message.symbolStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.symbolStatusRegulatoryHaltReason.isSome) &&& 252 = message.symbolStatusPresenceBits.val := by
    have clear := message.symbolStatusPresenceBits.property
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
  rw [selected_symbolStatusOperationalHaltReason]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_symbolStatusRegulatoryHaltReason]
  rw [decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_symbolStatusPresenceBits]; exact message.symbolStatusPresenceBits.property)]
  simp only [carried_symbolStatusPresenceBits]
  rfl

end SymbolStatusMessage

/-- Limit Order Accepted Message -/
structure LimitOrderAcceptedMessage where
  limitOrderAcceptedPresenceBits : Masked 32 32767
  transactTime : BitVec 64
  orderId : BitVec 64
  clOrdId : BitVec 64
  orderQty : BitVec 32
  limitOrderAcceptedBitFields : BitVec 32
  symbolId : BitVec 16
  price : BitVec 64
  limitOrderAcceptedSelfMatchScope : Option (BitVec 8)
  limitOrderAcceptedSelfMatchInstruction : Option (BitVec 8)
  limitOrderAcceptedPriceSlideInstruction : Option (BitVec 8)
  limitOrderAcceptedMinQty : Option (BitVec 32)
  limitOrderAcceptedMaxFloorQty : Option (BitVec 32)
  limitOrderAcceptedMaxReplenishQtyRange : Option (BitVec 32)
  limitOrderAcceptedMaxReplenishTimeRange : Option (BitVec 64)
  limitOrderAcceptedReferencePriceTarget : Option (BitVec 16)
  limitOrderAcceptedExpireTime : Option (BitVec 64)
  limitOrderAcceptedUserData : Option (BitVec 64)
  limitOrderAcceptedMpid : Option (Alpha 4)
  limitOrderAcceptedMemberGroup : Option (Alpha 2)
  limitOrderAcceptedLocateBroker : Option (Alpha 4)
  limitOrderAcceptedRankPrice : Option (BitVec 64)
  limitOrderAcceptedDisplayPrice : Option (BitVec 64)
  deriving DecidableEq, Repr

namespace LimitOrderAcceptedMessage

def encode (message : LimitOrderAcceptedMessage) : List UInt8 :=
  encodeUIntLE 4 (message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.limitOrderAcceptedBitFields
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeOptional (encodeUIntLE 1) message.limitOrderAcceptedSelfMatchScope
    ++ (encodeOptional (encodeUIntLE 1) message.limitOrderAcceptedSelfMatchInstruction
    ++ (encodeOptional (encodeUIntLE 1) message.limitOrderAcceptedPriceSlideInstruction
    ++ (encodeOptional (encodeUIntLE 4) message.limitOrderAcceptedMinQty
    ++ (encodeOptional (encodeUIntLE 4) message.limitOrderAcceptedMaxFloorQty
    ++ (encodeOptional (encodeUIntLE 4) message.limitOrderAcceptedMaxReplenishQtyRange
    ++ (encodeOptional (encodeUIntLE 8) message.limitOrderAcceptedMaxReplenishTimeRange
    ++ (encodeOptional (encodeUIntLE 2) message.limitOrderAcceptedReferencePriceTarget
    ++ (encodeOptional (encodeUIntLE 8) message.limitOrderAcceptedExpireTime
    ++ (encodeOptional (encodeUIntLE 8) message.limitOrderAcceptedUserData
    ++ (encodeOptional (Alpha.encode) message.limitOrderAcceptedMpid
    ++ (encodeOptional (Alpha.encode) message.limitOrderAcceptedMemberGroup
    ++ (encodeOptional (Alpha.encode) message.limitOrderAcceptedLocateBroker
    ++ (encodeOptional (encodeUIntLE 8) message.limitOrderAcceptedRankPrice
    ++ (encodeOptional (encodeUIntLE 8) message.limitOrderAcceptedDisplayPrice))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (LimitOrderAcceptedMessage × List UInt8) := do
  let (limitOrderAcceptedPresenceBits_, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (limitOrderAcceptedBitFields, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (limitOrderAcceptedSelfMatchScope, bytes) ← decodeOptional (decodeUIntLE 1) (limitOrderAcceptedPresenceBits_ &&& 1 != 0) bytes
  let (limitOrderAcceptedSelfMatchInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (limitOrderAcceptedPresenceBits_ &&& 2 != 0) bytes
  let (limitOrderAcceptedPriceSlideInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (limitOrderAcceptedPresenceBits_ &&& 4 != 0) bytes
  let (limitOrderAcceptedMinQty, bytes) ← decodeOptional (decodeUIntLE 4) (limitOrderAcceptedPresenceBits_ &&& 8 != 0) bytes
  let (limitOrderAcceptedMaxFloorQty, bytes) ← decodeOptional (decodeUIntLE 4) (limitOrderAcceptedPresenceBits_ &&& 16 != 0) bytes
  let (limitOrderAcceptedMaxReplenishQtyRange, bytes) ← decodeOptional (decodeUIntLE 4) (limitOrderAcceptedPresenceBits_ &&& 32 != 0) bytes
  let (limitOrderAcceptedMaxReplenishTimeRange, bytes) ← decodeOptional (decodeUIntLE 8) (limitOrderAcceptedPresenceBits_ &&& 64 != 0) bytes
  let (limitOrderAcceptedReferencePriceTarget, bytes) ← decodeOptional (decodeUIntLE 2) (limitOrderAcceptedPresenceBits_ &&& 128 != 0) bytes
  let (limitOrderAcceptedExpireTime, bytes) ← decodeOptional (decodeUIntLE 8) (limitOrderAcceptedPresenceBits_ &&& 256 != 0) bytes
  let (limitOrderAcceptedUserData, bytes) ← decodeOptional (decodeUIntLE 8) (limitOrderAcceptedPresenceBits_ &&& 512 != 0) bytes
  let (limitOrderAcceptedMpid, bytes) ← decodeOptional (Alpha.decode 4) (limitOrderAcceptedPresenceBits_ &&& 1024 != 0) bytes
  let (limitOrderAcceptedMemberGroup, bytes) ← decodeOptional (Alpha.decode 2) (limitOrderAcceptedPresenceBits_ &&& 2048 != 0) bytes
  let (limitOrderAcceptedLocateBroker, bytes) ← decodeOptional (Alpha.decode 4) (limitOrderAcceptedPresenceBits_ &&& 4096 != 0) bytes
  let (limitOrderAcceptedRankPrice, bytes) ← decodeOptional (decodeUIntLE 8) (limitOrderAcceptedPresenceBits_ &&& 8192 != 0) bytes
  let (limitOrderAcceptedDisplayPrice, bytes) ← decodeOptional (decodeUIntLE 8) (limitOrderAcceptedPresenceBits_ &&& 16384 != 0) bytes
  if fits_limitOrderAcceptedPresenceBits : (limitOrderAcceptedPresenceBits_ &&& 4294934528) &&& 32767 = 0 then
    pure ({ limitOrderAcceptedPresenceBits := ⟨limitOrderAcceptedPresenceBits_ &&& 4294934528, fits_limitOrderAcceptedPresenceBits⟩, transactTime, orderId, clOrdId, orderQty, limitOrderAcceptedBitFields, symbolId, price, limitOrderAcceptedSelfMatchScope, limitOrderAcceptedSelfMatchInstruction, limitOrderAcceptedPriceSlideInstruction, limitOrderAcceptedMinQty, limitOrderAcceptedMaxFloorQty, limitOrderAcceptedMaxReplenishQtyRange, limitOrderAcceptedMaxReplenishTimeRange, limitOrderAcceptedReferencePriceTarget, limitOrderAcceptedExpireTime, limitOrderAcceptedUserData, limitOrderAcceptedMpid, limitOrderAcceptedMemberGroup, limitOrderAcceptedLocateBroker, limitOrderAcceptedRankPrice, limitOrderAcceptedDisplayPrice }, bytes)
  else none

theorem encode_length_pos (message : LimitOrderAcceptedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : LimitOrderAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_limitOrderAcceptedSelfMatchScope : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 1 != 0) = message.limitOrderAcceptedSelfMatchScope.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedSelfMatchInstruction : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 2 != 0) = message.limitOrderAcceptedSelfMatchInstruction.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedPriceSlideInstruction : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 4 != 0) = message.limitOrderAcceptedPriceSlideInstruction.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedMinQty : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 8 != 0) = message.limitOrderAcceptedMinQty.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedMaxFloorQty : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 16 != 0) = message.limitOrderAcceptedMaxFloorQty.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedMaxReplenishQtyRange : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 32 != 0) = message.limitOrderAcceptedMaxReplenishQtyRange.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedMaxReplenishTimeRange : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 64 != 0) = message.limitOrderAcceptedMaxReplenishTimeRange.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedReferencePriceTarget : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 128 != 0) = message.limitOrderAcceptedReferencePriceTarget.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedExpireTime : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 256 != 0) = message.limitOrderAcceptedExpireTime.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedUserData : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 512 != 0) = message.limitOrderAcceptedUserData.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedMpid : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 1024 != 0) = message.limitOrderAcceptedMpid.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedMemberGroup : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 2048 != 0) = message.limitOrderAcceptedMemberGroup.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedLocateBroker : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 4096 != 0) = message.limitOrderAcceptedLocateBroker.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedRankPrice : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 8192 != 0) = message.limitOrderAcceptedRankPrice.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderAcceptedDisplayPrice : ((message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 16384 != 0) = message.limitOrderAcceptedDisplayPrice.isSome := by
    have clear := message.limitOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_limitOrderAcceptedPresenceBits : (message.limitOrderAcceptedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderAcceptedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderAcceptedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderAcceptedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderAcceptedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderAcceptedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderAcceptedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderAcceptedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderAcceptedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderAcceptedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderAcceptedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderAcceptedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderAcceptedLocateBroker.isSome ||| presence (n := 32) 8192 message.limitOrderAcceptedRankPrice.isSome ||| presence (n := 32) 16384 message.limitOrderAcceptedDisplayPrice.isSome) &&& 4294934528 = message.limitOrderAcceptedPresenceBits.val := by
    have clear := message.limitOrderAcceptedPresenceBits.property
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedSelfMatchScope]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedSelfMatchInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedPriceSlideInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedMinQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedMaxFloorQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedMaxReplenishQtyRange]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedMaxReplenishTimeRange]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedReferencePriceTarget]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 2) (decodeUIntLE 2) (decodeUIntLE_encodeUIntLE 2), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedExpireTime]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedUserData]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedMpid]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedMemberGroup]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 2) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedLocateBroker]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedRankPrice]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_limitOrderAcceptedDisplayPrice]
  rw [decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_limitOrderAcceptedPresenceBits]; exact message.limitOrderAcceptedPresenceBits.property)]
  simp only [carried_limitOrderAcceptedPresenceBits]
  rfl

end LimitOrderAcceptedMessage

/-- Limit Order Rejected Message -/
structure LimitOrderRejectedMessage where
  limitOrderRejectedPresenceBits : Masked 32 8191
  transactTime : BitVec 64
  clOrdId : BitVec 64
  orderQty : BitVec 32
  limitOrderRejectedBitFields : BitVec 32
  symbolId : BitVec 16
  price : BitVec 64
  limitOrderRejectedReason : BitVec 8
  limitOrderRejectedSelfMatchScope : Option (BitVec 8)
  limitOrderRejectedSelfMatchInstruction : Option (BitVec 8)
  limitOrderRejectedPriceSlideInstruction : Option (BitVec 8)
  limitOrderRejectedMinQty : Option (BitVec 32)
  limitOrderRejectedMaxFloorQty : Option (BitVec 32)
  limitOrderRejectedMaxReplenishQtyRange : Option (BitVec 32)
  limitOrderRejectedMaxReplenishTimeRange : Option (BitVec 64)
  limitOrderRejectedReferencePriceTarget : Option (BitVec 16)
  limitOrderRejectedExpireTime : Option (BitVec 64)
  limitOrderRejectedUserData : Option (BitVec 64)
  limitOrderRejectedMpid : Option (Alpha 4)
  limitOrderRejectedMemberGroup : Option (Alpha 2)
  limitOrderRejectedLocateBroker : Option (Alpha 4)
  deriving DecidableEq, Repr

namespace LimitOrderRejectedMessage

def encode (message : LimitOrderRejectedMessage) : List UInt8 :=
  encodeUIntLE 4 (message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.limitOrderRejectedBitFields
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 1 message.limitOrderRejectedReason
    ++ (encodeOptional (encodeUIntLE 1) message.limitOrderRejectedSelfMatchScope
    ++ (encodeOptional (encodeUIntLE 1) message.limitOrderRejectedSelfMatchInstruction
    ++ (encodeOptional (encodeUIntLE 1) message.limitOrderRejectedPriceSlideInstruction
    ++ (encodeOptional (encodeUIntLE 4) message.limitOrderRejectedMinQty
    ++ (encodeOptional (encodeUIntLE 4) message.limitOrderRejectedMaxFloorQty
    ++ (encodeOptional (encodeUIntLE 4) message.limitOrderRejectedMaxReplenishQtyRange
    ++ (encodeOptional (encodeUIntLE 8) message.limitOrderRejectedMaxReplenishTimeRange
    ++ (encodeOptional (encodeUIntLE 2) message.limitOrderRejectedReferencePriceTarget
    ++ (encodeOptional (encodeUIntLE 8) message.limitOrderRejectedExpireTime
    ++ (encodeOptional (encodeUIntLE 8) message.limitOrderRejectedUserData
    ++ (encodeOptional (Alpha.encode) message.limitOrderRejectedMpid
    ++ (encodeOptional (Alpha.encode) message.limitOrderRejectedMemberGroup
    ++ (encodeOptional (Alpha.encode) message.limitOrderRejectedLocateBroker))))))))))))))))))))

def decode (bytes : List UInt8) : Option (LimitOrderRejectedMessage × List UInt8) := do
  let (limitOrderRejectedPresenceBits_, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (limitOrderRejectedBitFields, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (limitOrderRejectedReason, bytes) ← decodeUIntLE 1 bytes
  let (limitOrderRejectedSelfMatchScope, bytes) ← decodeOptional (decodeUIntLE 1) (limitOrderRejectedPresenceBits_ &&& 1 != 0) bytes
  let (limitOrderRejectedSelfMatchInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (limitOrderRejectedPresenceBits_ &&& 2 != 0) bytes
  let (limitOrderRejectedPriceSlideInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (limitOrderRejectedPresenceBits_ &&& 4 != 0) bytes
  let (limitOrderRejectedMinQty, bytes) ← decodeOptional (decodeUIntLE 4) (limitOrderRejectedPresenceBits_ &&& 8 != 0) bytes
  let (limitOrderRejectedMaxFloorQty, bytes) ← decodeOptional (decodeUIntLE 4) (limitOrderRejectedPresenceBits_ &&& 16 != 0) bytes
  let (limitOrderRejectedMaxReplenishQtyRange, bytes) ← decodeOptional (decodeUIntLE 4) (limitOrderRejectedPresenceBits_ &&& 32 != 0) bytes
  let (limitOrderRejectedMaxReplenishTimeRange, bytes) ← decodeOptional (decodeUIntLE 8) (limitOrderRejectedPresenceBits_ &&& 64 != 0) bytes
  let (limitOrderRejectedReferencePriceTarget, bytes) ← decodeOptional (decodeUIntLE 2) (limitOrderRejectedPresenceBits_ &&& 128 != 0) bytes
  let (limitOrderRejectedExpireTime, bytes) ← decodeOptional (decodeUIntLE 8) (limitOrderRejectedPresenceBits_ &&& 256 != 0) bytes
  let (limitOrderRejectedUserData, bytes) ← decodeOptional (decodeUIntLE 8) (limitOrderRejectedPresenceBits_ &&& 512 != 0) bytes
  let (limitOrderRejectedMpid, bytes) ← decodeOptional (Alpha.decode 4) (limitOrderRejectedPresenceBits_ &&& 1024 != 0) bytes
  let (limitOrderRejectedMemberGroup, bytes) ← decodeOptional (Alpha.decode 2) (limitOrderRejectedPresenceBits_ &&& 2048 != 0) bytes
  let (limitOrderRejectedLocateBroker, bytes) ← decodeOptional (Alpha.decode 4) (limitOrderRejectedPresenceBits_ &&& 4096 != 0) bytes
  if fits_limitOrderRejectedPresenceBits : (limitOrderRejectedPresenceBits_ &&& 4294959104) &&& 8191 = 0 then
    pure ({ limitOrderRejectedPresenceBits := ⟨limitOrderRejectedPresenceBits_ &&& 4294959104, fits_limitOrderRejectedPresenceBits⟩, transactTime, clOrdId, orderQty, limitOrderRejectedBitFields, symbolId, price, limitOrderRejectedReason, limitOrderRejectedSelfMatchScope, limitOrderRejectedSelfMatchInstruction, limitOrderRejectedPriceSlideInstruction, limitOrderRejectedMinQty, limitOrderRejectedMaxFloorQty, limitOrderRejectedMaxReplenishQtyRange, limitOrderRejectedMaxReplenishTimeRange, limitOrderRejectedReferencePriceTarget, limitOrderRejectedExpireTime, limitOrderRejectedUserData, limitOrderRejectedMpid, limitOrderRejectedMemberGroup, limitOrderRejectedLocateBroker }, bytes)
  else none

theorem encode_length_pos (message : LimitOrderRejectedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : LimitOrderRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_limitOrderRejectedSelfMatchScope : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 1 != 0) = message.limitOrderRejectedSelfMatchScope.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderRejectedSelfMatchInstruction : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 2 != 0) = message.limitOrderRejectedSelfMatchInstruction.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderRejectedPriceSlideInstruction : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 4 != 0) = message.limitOrderRejectedPriceSlideInstruction.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderRejectedMinQty : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 8 != 0) = message.limitOrderRejectedMinQty.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderRejectedMaxFloorQty : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 16 != 0) = message.limitOrderRejectedMaxFloorQty.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderRejectedMaxReplenishQtyRange : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 32 != 0) = message.limitOrderRejectedMaxReplenishQtyRange.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderRejectedMaxReplenishTimeRange : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 64 != 0) = message.limitOrderRejectedMaxReplenishTimeRange.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderRejectedReferencePriceTarget : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 128 != 0) = message.limitOrderRejectedReferencePriceTarget.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderRejectedExpireTime : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 256 != 0) = message.limitOrderRejectedExpireTime.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderRejectedUserData : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 512 != 0) = message.limitOrderRejectedUserData.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderRejectedMpid : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 1024 != 0) = message.limitOrderRejectedMpid.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderRejectedMemberGroup : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 2048 != 0) = message.limitOrderRejectedMemberGroup.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_limitOrderRejectedLocateBroker : ((message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 4096 != 0) = message.limitOrderRejectedLocateBroker.isSome := by
    have clear := message.limitOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_limitOrderRejectedPresenceBits : (message.limitOrderRejectedPresenceBits.val ||| presence (n := 32) 1 message.limitOrderRejectedSelfMatchScope.isSome ||| presence (n := 32) 2 message.limitOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 32) 4 message.limitOrderRejectedPriceSlideInstruction.isSome ||| presence (n := 32) 8 message.limitOrderRejectedMinQty.isSome ||| presence (n := 32) 16 message.limitOrderRejectedMaxFloorQty.isSome ||| presence (n := 32) 32 message.limitOrderRejectedMaxReplenishQtyRange.isSome ||| presence (n := 32) 64 message.limitOrderRejectedMaxReplenishTimeRange.isSome ||| presence (n := 32) 128 message.limitOrderRejectedReferencePriceTarget.isSome ||| presence (n := 32) 256 message.limitOrderRejectedExpireTime.isSome ||| presence (n := 32) 512 message.limitOrderRejectedUserData.isSome ||| presence (n := 32) 1024 message.limitOrderRejectedMpid.isSome ||| presence (n := 32) 2048 message.limitOrderRejectedMemberGroup.isSome ||| presence (n := 32) 4096 message.limitOrderRejectedLocateBroker.isSome) &&& 4294959104 = message.limitOrderRejectedPresenceBits.val := by
    have clear := message.limitOrderRejectedPresenceBits.property
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_limitOrderRejectedSelfMatchScope]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_limitOrderRejectedSelfMatchInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_limitOrderRejectedPriceSlideInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_limitOrderRejectedMinQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_limitOrderRejectedMaxFloorQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_limitOrderRejectedMaxReplenishQtyRange]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_limitOrderRejectedMaxReplenishTimeRange]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_limitOrderRejectedReferencePriceTarget]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 2) (decodeUIntLE 2) (decodeUIntLE_encodeUIntLE 2), some_bind]
  dsimp only
  rw [selected_limitOrderRejectedExpireTime]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_limitOrderRejectedUserData]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_limitOrderRejectedMpid]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_limitOrderRejectedMemberGroup]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 2) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_limitOrderRejectedLocateBroker]
  rw [decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_limitOrderRejectedPresenceBits]; exact message.limitOrderRejectedPresenceBits.property)]
  simp only [carried_limitOrderRejectedPresenceBits]
  rfl

end LimitOrderRejectedMessage

/-- Market Order Accepted Message -/
structure MarketOrderAcceptedMessage where
  marketOrderAcceptedPresenceBits : Masked 16 63
  transactTime : BitVec 64
  orderId : BitVec 64
  clOrdId : BitVec 64
  orderQty : BitVec 32
  marketOrderAcceptedBitFields : BitVec 16
  symbolId : BitVec 16
  marketOrderAcceptedSelfMatchScope : Option (BitVec 8)
  marketOrderAcceptedSelfMatchInstruction : Option (BitVec 8)
  marketOrderAcceptedUserData : Option (BitVec 64)
  marketOrderAcceptedMpid : Option (Alpha 4)
  marketOrderAcceptedMemberGroup : Option (Alpha 2)
  marketOrderAcceptedLocateBroker : Option (Alpha 4)
  deriving DecidableEq, Repr

namespace MarketOrderAcceptedMessage

def encode (message : MarketOrderAcceptedMessage) : List UInt8 :=
  encodeUIntLE 2 (message.marketOrderAcceptedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderAcceptedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderAcceptedUserData.isSome ||| presence (n := 16) 8 message.marketOrderAcceptedMpid.isSome ||| presence (n := 16) 16 message.marketOrderAcceptedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderAcceptedLocateBroker.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 2 message.marketOrderAcceptedBitFields
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeOptional (encodeUIntLE 1) message.marketOrderAcceptedSelfMatchScope
    ++ (encodeOptional (encodeUIntLE 1) message.marketOrderAcceptedSelfMatchInstruction
    ++ (encodeOptional (encodeUIntLE 8) message.marketOrderAcceptedUserData
    ++ (encodeOptional (Alpha.encode) message.marketOrderAcceptedMpid
    ++ (encodeOptional (Alpha.encode) message.marketOrderAcceptedMemberGroup
    ++ (encodeOptional (Alpha.encode) message.marketOrderAcceptedLocateBroker))))))))))))

def decode (bytes : List UInt8) : Option (MarketOrderAcceptedMessage × List UInt8) := do
  let (marketOrderAcceptedPresenceBits_, bytes) ← decodeUIntLE 2 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (marketOrderAcceptedBitFields, bytes) ← decodeUIntLE 2 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (marketOrderAcceptedSelfMatchScope, bytes) ← decodeOptional (decodeUIntLE 1) (marketOrderAcceptedPresenceBits_ &&& 1 != 0) bytes
  let (marketOrderAcceptedSelfMatchInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (marketOrderAcceptedPresenceBits_ &&& 2 != 0) bytes
  let (marketOrderAcceptedUserData, bytes) ← decodeOptional (decodeUIntLE 8) (marketOrderAcceptedPresenceBits_ &&& 4 != 0) bytes
  let (marketOrderAcceptedMpid, bytes) ← decodeOptional (Alpha.decode 4) (marketOrderAcceptedPresenceBits_ &&& 8 != 0) bytes
  let (marketOrderAcceptedMemberGroup, bytes) ← decodeOptional (Alpha.decode 2) (marketOrderAcceptedPresenceBits_ &&& 16 != 0) bytes
  let (marketOrderAcceptedLocateBroker, bytes) ← decodeOptional (Alpha.decode 4) (marketOrderAcceptedPresenceBits_ &&& 32 != 0) bytes
  if fits_marketOrderAcceptedPresenceBits : (marketOrderAcceptedPresenceBits_ &&& 65472) &&& 63 = 0 then
    pure ({ marketOrderAcceptedPresenceBits := ⟨marketOrderAcceptedPresenceBits_ &&& 65472, fits_marketOrderAcceptedPresenceBits⟩, transactTime, orderId, clOrdId, orderQty, marketOrderAcceptedBitFields, symbolId, marketOrderAcceptedSelfMatchScope, marketOrderAcceptedSelfMatchInstruction, marketOrderAcceptedUserData, marketOrderAcceptedMpid, marketOrderAcceptedMemberGroup, marketOrderAcceptedLocateBroker }, bytes)
  else none

theorem encode_length_pos (message : MarketOrderAcceptedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : MarketOrderAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_marketOrderAcceptedSelfMatchScope : ((message.marketOrderAcceptedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderAcceptedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderAcceptedUserData.isSome ||| presence (n := 16) 8 message.marketOrderAcceptedMpid.isSome ||| presence (n := 16) 16 message.marketOrderAcceptedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderAcceptedLocateBroker.isSome) &&& 1 != 0) = message.marketOrderAcceptedSelfMatchScope.isSome := by
    have clear := message.marketOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderAcceptedSelfMatchInstruction : ((message.marketOrderAcceptedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderAcceptedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderAcceptedUserData.isSome ||| presence (n := 16) 8 message.marketOrderAcceptedMpid.isSome ||| presence (n := 16) 16 message.marketOrderAcceptedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderAcceptedLocateBroker.isSome) &&& 2 != 0) = message.marketOrderAcceptedSelfMatchInstruction.isSome := by
    have clear := message.marketOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderAcceptedUserData : ((message.marketOrderAcceptedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderAcceptedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderAcceptedUserData.isSome ||| presence (n := 16) 8 message.marketOrderAcceptedMpid.isSome ||| presence (n := 16) 16 message.marketOrderAcceptedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderAcceptedLocateBroker.isSome) &&& 4 != 0) = message.marketOrderAcceptedUserData.isSome := by
    have clear := message.marketOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderAcceptedMpid : ((message.marketOrderAcceptedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderAcceptedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderAcceptedUserData.isSome ||| presence (n := 16) 8 message.marketOrderAcceptedMpid.isSome ||| presence (n := 16) 16 message.marketOrderAcceptedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderAcceptedLocateBroker.isSome) &&& 8 != 0) = message.marketOrderAcceptedMpid.isSome := by
    have clear := message.marketOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderAcceptedMemberGroup : ((message.marketOrderAcceptedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderAcceptedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderAcceptedUserData.isSome ||| presence (n := 16) 8 message.marketOrderAcceptedMpid.isSome ||| presence (n := 16) 16 message.marketOrderAcceptedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderAcceptedLocateBroker.isSome) &&& 16 != 0) = message.marketOrderAcceptedMemberGroup.isSome := by
    have clear := message.marketOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderAcceptedLocateBroker : ((message.marketOrderAcceptedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderAcceptedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderAcceptedUserData.isSome ||| presence (n := 16) 8 message.marketOrderAcceptedMpid.isSome ||| presence (n := 16) 16 message.marketOrderAcceptedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderAcceptedLocateBroker.isSome) &&& 32 != 0) = message.marketOrderAcceptedLocateBroker.isSome := by
    have clear := message.marketOrderAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_marketOrderAcceptedPresenceBits : (message.marketOrderAcceptedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderAcceptedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderAcceptedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderAcceptedUserData.isSome ||| presence (n := 16) 8 message.marketOrderAcceptedMpid.isSome ||| presence (n := 16) 16 message.marketOrderAcceptedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderAcceptedLocateBroker.isSome) &&& 65472 = message.marketOrderAcceptedPresenceBits.val := by
    have clear := message.marketOrderAcceptedPresenceBits.property
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_marketOrderAcceptedSelfMatchScope]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_marketOrderAcceptedSelfMatchInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_marketOrderAcceptedUserData]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_marketOrderAcceptedMpid]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_marketOrderAcceptedMemberGroup]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 2) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_marketOrderAcceptedLocateBroker]
  rw [decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_marketOrderAcceptedPresenceBits]; exact message.marketOrderAcceptedPresenceBits.property)]
  simp only [carried_marketOrderAcceptedPresenceBits]
  rfl

end MarketOrderAcceptedMessage

/-- Market Order Rejected Message -/
structure MarketOrderRejectedMessage where
  marketOrderRejectedPresenceBits : Masked 16 63
  transactTime : BitVec 64
  clOrdId : BitVec 64
  orderQty : BitVec 32
  marketOrderRejectedBitFields : BitVec 16
  symbolId : BitVec 16
  marketOrderRejectedReason : BitVec 8
  marketOrderRejectedSelfMatchScope : Option (BitVec 8)
  marketOrderRejectedSelfMatchInstruction : Option (BitVec 8)
  marketOrderRejectedUserData : Option (BitVec 64)
  marketOrderRejectedMpid : Option (Alpha 4)
  marketOrderRejectedMemberGroup : Option (Alpha 2)
  marketOrderRejectedLocateBroker : Option (Alpha 4)
  deriving DecidableEq, Repr

namespace MarketOrderRejectedMessage

def encode (message : MarketOrderRejectedMessage) : List UInt8 :=
  encodeUIntLE 2 (message.marketOrderRejectedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderRejectedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderRejectedUserData.isSome ||| presence (n := 16) 8 message.marketOrderRejectedMpid.isSome ||| presence (n := 16) 16 message.marketOrderRejectedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderRejectedLocateBroker.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 2 message.marketOrderRejectedBitFields
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 1 message.marketOrderRejectedReason
    ++ (encodeOptional (encodeUIntLE 1) message.marketOrderRejectedSelfMatchScope
    ++ (encodeOptional (encodeUIntLE 1) message.marketOrderRejectedSelfMatchInstruction
    ++ (encodeOptional (encodeUIntLE 8) message.marketOrderRejectedUserData
    ++ (encodeOptional (Alpha.encode) message.marketOrderRejectedMpid
    ++ (encodeOptional (Alpha.encode) message.marketOrderRejectedMemberGroup
    ++ (encodeOptional (Alpha.encode) message.marketOrderRejectedLocateBroker))))))))))))

def decode (bytes : List UInt8) : Option (MarketOrderRejectedMessage × List UInt8) := do
  let (marketOrderRejectedPresenceBits_, bytes) ← decodeUIntLE 2 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (marketOrderRejectedBitFields, bytes) ← decodeUIntLE 2 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (marketOrderRejectedReason, bytes) ← decodeUIntLE 1 bytes
  let (marketOrderRejectedSelfMatchScope, bytes) ← decodeOptional (decodeUIntLE 1) (marketOrderRejectedPresenceBits_ &&& 1 != 0) bytes
  let (marketOrderRejectedSelfMatchInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (marketOrderRejectedPresenceBits_ &&& 2 != 0) bytes
  let (marketOrderRejectedUserData, bytes) ← decodeOptional (decodeUIntLE 8) (marketOrderRejectedPresenceBits_ &&& 4 != 0) bytes
  let (marketOrderRejectedMpid, bytes) ← decodeOptional (Alpha.decode 4) (marketOrderRejectedPresenceBits_ &&& 8 != 0) bytes
  let (marketOrderRejectedMemberGroup, bytes) ← decodeOptional (Alpha.decode 2) (marketOrderRejectedPresenceBits_ &&& 16 != 0) bytes
  let (marketOrderRejectedLocateBroker, bytes) ← decodeOptional (Alpha.decode 4) (marketOrderRejectedPresenceBits_ &&& 32 != 0) bytes
  if fits_marketOrderRejectedPresenceBits : (marketOrderRejectedPresenceBits_ &&& 65472) &&& 63 = 0 then
    pure ({ marketOrderRejectedPresenceBits := ⟨marketOrderRejectedPresenceBits_ &&& 65472, fits_marketOrderRejectedPresenceBits⟩, transactTime, clOrdId, orderQty, marketOrderRejectedBitFields, symbolId, marketOrderRejectedReason, marketOrderRejectedSelfMatchScope, marketOrderRejectedSelfMatchInstruction, marketOrderRejectedUserData, marketOrderRejectedMpid, marketOrderRejectedMemberGroup, marketOrderRejectedLocateBroker }, bytes)
  else none

theorem encode_length_pos (message : MarketOrderRejectedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : MarketOrderRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_marketOrderRejectedSelfMatchScope : ((message.marketOrderRejectedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderRejectedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderRejectedUserData.isSome ||| presence (n := 16) 8 message.marketOrderRejectedMpid.isSome ||| presence (n := 16) 16 message.marketOrderRejectedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderRejectedLocateBroker.isSome) &&& 1 != 0) = message.marketOrderRejectedSelfMatchScope.isSome := by
    have clear := message.marketOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderRejectedSelfMatchInstruction : ((message.marketOrderRejectedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderRejectedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderRejectedUserData.isSome ||| presence (n := 16) 8 message.marketOrderRejectedMpid.isSome ||| presence (n := 16) 16 message.marketOrderRejectedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderRejectedLocateBroker.isSome) &&& 2 != 0) = message.marketOrderRejectedSelfMatchInstruction.isSome := by
    have clear := message.marketOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderRejectedUserData : ((message.marketOrderRejectedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderRejectedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderRejectedUserData.isSome ||| presence (n := 16) 8 message.marketOrderRejectedMpid.isSome ||| presence (n := 16) 16 message.marketOrderRejectedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderRejectedLocateBroker.isSome) &&& 4 != 0) = message.marketOrderRejectedUserData.isSome := by
    have clear := message.marketOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderRejectedMpid : ((message.marketOrderRejectedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderRejectedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderRejectedUserData.isSome ||| presence (n := 16) 8 message.marketOrderRejectedMpid.isSome ||| presence (n := 16) 16 message.marketOrderRejectedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderRejectedLocateBroker.isSome) &&& 8 != 0) = message.marketOrderRejectedMpid.isSome := by
    have clear := message.marketOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderRejectedMemberGroup : ((message.marketOrderRejectedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderRejectedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderRejectedUserData.isSome ||| presence (n := 16) 8 message.marketOrderRejectedMpid.isSome ||| presence (n := 16) 16 message.marketOrderRejectedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderRejectedLocateBroker.isSome) &&& 16 != 0) = message.marketOrderRejectedMemberGroup.isSome := by
    have clear := message.marketOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_marketOrderRejectedLocateBroker : ((message.marketOrderRejectedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderRejectedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderRejectedUserData.isSome ||| presence (n := 16) 8 message.marketOrderRejectedMpid.isSome ||| presence (n := 16) 16 message.marketOrderRejectedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderRejectedLocateBroker.isSome) &&& 32 != 0) = message.marketOrderRejectedLocateBroker.isSome := by
    have clear := message.marketOrderRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_marketOrderRejectedPresenceBits : (message.marketOrderRejectedPresenceBits.val ||| presence (n := 16) 1 message.marketOrderRejectedSelfMatchScope.isSome ||| presence (n := 16) 2 message.marketOrderRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 4 message.marketOrderRejectedUserData.isSome ||| presence (n := 16) 8 message.marketOrderRejectedMpid.isSome ||| presence (n := 16) 16 message.marketOrderRejectedMemberGroup.isSome ||| presence (n := 16) 32 message.marketOrderRejectedLocateBroker.isSome) &&& 65472 = message.marketOrderRejectedPresenceBits.val := by
    have clear := message.marketOrderRejectedPresenceBits.property
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_marketOrderRejectedSelfMatchScope]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_marketOrderRejectedSelfMatchInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_marketOrderRejectedUserData]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_marketOrderRejectedMpid]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_marketOrderRejectedMemberGroup]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 2) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_marketOrderRejectedLocateBroker]
  rw [decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_marketOrderRejectedPresenceBits]; exact message.marketOrderRejectedPresenceBits.property)]
  simp only [carried_marketOrderRejectedPresenceBits]
  rfl

end MarketOrderRejectedMessage

/-- Order Canceled Message: 25 bytes -/
structure OrderCanceledMessage where
  transactTime : BitVec 64
  orderId : BitVec 64
  origClOrdId : BitVec 64
  cancelReason : BitVec 8
  deriving DecidableEq, Repr

namespace OrderCanceledMessage

def encode (message : OrderCanceledMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 1 message.cancelReason)))

def decode (bytes : List UInt8) : Option (OrderCanceledMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (cancelReason, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, orderId, origClOrdId, cancelReason }, bytes)

@[simp] theorem encode_length (message : OrderCanceledMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCanceledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCanceledMessage

/-- Cancel Rejected Message: 17 bytes -/
structure CancelRejectedMessage where
  transactTime : BitVec 64
  origClOrdId : BitVec 64
  cancelRejectedReason : BitVec 8
  deriving DecidableEq, Repr

namespace CancelRejectedMessage

def encode (message : CancelRejectedMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 1 message.cancelRejectedReason))

def decode (bytes : List UInt8) : Option (CancelRejectedMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (cancelRejectedReason, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, origClOrdId, cancelRejectedReason }, bytes)

@[simp] theorem encode_length (message : CancelRejectedMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : CancelRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CancelRejectedMessage

/-- Order Modified Message -/
structure OrderModifiedMessage where
  orderModifiedPresenceBits : Masked 8 7
  transactTime : BitVec 64
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  leavesQty : BitVec 32
  orderModifiedOrderQty : Option (BitVec 32)
  orderModifiedBitFields : Option (BitVec 8)
  orderModifiedLocateBroker : Option (Alpha 4)
  deriving DecidableEq, Repr

namespace OrderModifiedMessage

def encode (message : OrderModifiedMessage) : List UInt8 :=
  encodeUIntLE 1 (message.orderModifiedPresenceBits.val ||| presence (n := 8) 1 message.orderModifiedOrderQty.isSome ||| presence (n := 8) 2 message.orderModifiedBitFields.isSome ||| presence (n := 8) 4 message.orderModifiedLocateBroker.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeOptional (encodeUIntLE 4) message.orderModifiedOrderQty
    ++ (encodeOptional (encodeUIntLE 1) message.orderModifiedBitFields
    ++ (encodeOptional (Alpha.encode) message.orderModifiedLocateBroker))))))))

def decode (bytes : List UInt8) : Option (OrderModifiedMessage × List UInt8) := do
  let (orderModifiedPresenceBits_, bytes) ← decodeUIntLE 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (orderModifiedOrderQty, bytes) ← decodeOptional (decodeUIntLE 4) (orderModifiedPresenceBits_ &&& 1 != 0) bytes
  let (orderModifiedBitFields, bytes) ← decodeOptional (decodeUIntLE 1) (orderModifiedPresenceBits_ &&& 2 != 0) bytes
  let (orderModifiedLocateBroker, bytes) ← decodeOptional (Alpha.decode 4) (orderModifiedPresenceBits_ &&& 4 != 0) bytes
  if fits_orderModifiedPresenceBits : (orderModifiedPresenceBits_ &&& 248) &&& 7 = 0 then
    pure ({ orderModifiedPresenceBits := ⟨orderModifiedPresenceBits_ &&& 248, fits_orderModifiedPresenceBits⟩, transactTime, orderId, clOrdId, origClOrdId, leavesQty, orderModifiedOrderQty, orderModifiedBitFields, orderModifiedLocateBroker }, bytes)
  else none

theorem encode_length_pos (message : OrderModifiedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : OrderModifiedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_orderModifiedOrderQty : ((message.orderModifiedPresenceBits.val ||| presence (n := 8) 1 message.orderModifiedOrderQty.isSome ||| presence (n := 8) 2 message.orderModifiedBitFields.isSome ||| presence (n := 8) 4 message.orderModifiedLocateBroker.isSome) &&& 1 != 0) = message.orderModifiedOrderQty.isSome := by
    have clear := message.orderModifiedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_orderModifiedBitFields : ((message.orderModifiedPresenceBits.val ||| presence (n := 8) 1 message.orderModifiedOrderQty.isSome ||| presence (n := 8) 2 message.orderModifiedBitFields.isSome ||| presence (n := 8) 4 message.orderModifiedLocateBroker.isSome) &&& 2 != 0) = message.orderModifiedBitFields.isSome := by
    have clear := message.orderModifiedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_orderModifiedLocateBroker : ((message.orderModifiedPresenceBits.val ||| presence (n := 8) 1 message.orderModifiedOrderQty.isSome ||| presence (n := 8) 2 message.orderModifiedBitFields.isSome ||| presence (n := 8) 4 message.orderModifiedLocateBroker.isSome) &&& 4 != 0) = message.orderModifiedLocateBroker.isSome := by
    have clear := message.orderModifiedPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_orderModifiedPresenceBits : (message.orderModifiedPresenceBits.val ||| presence (n := 8) 1 message.orderModifiedOrderQty.isSome ||| presence (n := 8) 2 message.orderModifiedBitFields.isSome ||| presence (n := 8) 4 message.orderModifiedLocateBroker.isSome) &&& 248 = message.orderModifiedPresenceBits.val := by
    have clear := message.orderModifiedPresenceBits.property
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
  rw [selected_orderModifiedOrderQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_orderModifiedBitFields]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_orderModifiedLocateBroker]
  rw [decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_orderModifiedPresenceBits]; exact message.orderModifiedPresenceBits.property)]
  simp only [carried_orderModifiedPresenceBits]
  rfl

end OrderModifiedMessage

/-- Modify Rejected Message -/
structure ModifyRejectedMessage where
  modifyRejectedPresenceBits : Masked 8 7
  transactTime : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  modifyRejectedReason : BitVec 8
  modifyRejectedOrderQty : Option (BitVec 32)
  modifyRejectedBitFields : Option (BitVec 8)
  modifyRejectedLocateBroker : Option (Alpha 4)
  deriving DecidableEq, Repr

namespace ModifyRejectedMessage

def encode (message : ModifyRejectedMessage) : List UInt8 :=
  encodeUIntLE 1 (message.modifyRejectedPresenceBits.val ||| presence (n := 8) 1 message.modifyRejectedOrderQty.isSome ||| presence (n := 8) 2 message.modifyRejectedBitFields.isSome ||| presence (n := 8) 4 message.modifyRejectedLocateBroker.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 1 message.modifyRejectedReason
    ++ (encodeOptional (encodeUIntLE 4) message.modifyRejectedOrderQty
    ++ (encodeOptional (encodeUIntLE 1) message.modifyRejectedBitFields
    ++ (encodeOptional (Alpha.encode) message.modifyRejectedLocateBroker)))))))

def decode (bytes : List UInt8) : Option (ModifyRejectedMessage × List UInt8) := do
  let (modifyRejectedPresenceBits_, bytes) ← decodeUIntLE 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (modifyRejectedReason, bytes) ← decodeUIntLE 1 bytes
  let (modifyRejectedOrderQty, bytes) ← decodeOptional (decodeUIntLE 4) (modifyRejectedPresenceBits_ &&& 1 != 0) bytes
  let (modifyRejectedBitFields, bytes) ← decodeOptional (decodeUIntLE 1) (modifyRejectedPresenceBits_ &&& 2 != 0) bytes
  let (modifyRejectedLocateBroker, bytes) ← decodeOptional (Alpha.decode 4) (modifyRejectedPresenceBits_ &&& 4 != 0) bytes
  if fits_modifyRejectedPresenceBits : (modifyRejectedPresenceBits_ &&& 248) &&& 7 = 0 then
    pure ({ modifyRejectedPresenceBits := ⟨modifyRejectedPresenceBits_ &&& 248, fits_modifyRejectedPresenceBits⟩, transactTime, clOrdId, origClOrdId, modifyRejectedReason, modifyRejectedOrderQty, modifyRejectedBitFields, modifyRejectedLocateBroker }, bytes)
  else none

theorem encode_length_pos (message : ModifyRejectedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : ModifyRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_modifyRejectedOrderQty : ((message.modifyRejectedPresenceBits.val ||| presence (n := 8) 1 message.modifyRejectedOrderQty.isSome ||| presence (n := 8) 2 message.modifyRejectedBitFields.isSome ||| presence (n := 8) 4 message.modifyRejectedLocateBroker.isSome) &&& 1 != 0) = message.modifyRejectedOrderQty.isSome := by
    have clear := message.modifyRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_modifyRejectedBitFields : ((message.modifyRejectedPresenceBits.val ||| presence (n := 8) 1 message.modifyRejectedOrderQty.isSome ||| presence (n := 8) 2 message.modifyRejectedBitFields.isSome ||| presence (n := 8) 4 message.modifyRejectedLocateBroker.isSome) &&& 2 != 0) = message.modifyRejectedBitFields.isSome := by
    have clear := message.modifyRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_modifyRejectedLocateBroker : ((message.modifyRejectedPresenceBits.val ||| presence (n := 8) 1 message.modifyRejectedOrderQty.isSome ||| presence (n := 8) 2 message.modifyRejectedBitFields.isSome ||| presence (n := 8) 4 message.modifyRejectedLocateBroker.isSome) &&& 4 != 0) = message.modifyRejectedLocateBroker.isSome := by
    have clear := message.modifyRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_modifyRejectedPresenceBits : (message.modifyRejectedPresenceBits.val ||| presence (n := 8) 1 message.modifyRejectedOrderQty.isSome ||| presence (n := 8) 2 message.modifyRejectedBitFields.isSome ||| presence (n := 8) 4 message.modifyRejectedLocateBroker.isSome) &&& 248 = message.modifyRejectedPresenceBits.val := by
    have clear := message.modifyRejectedPresenceBits.property
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
  rw [selected_modifyRejectedOrderQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_modifyRejectedBitFields]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_modifyRejectedLocateBroker]
  rw [decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_modifyRejectedPresenceBits]; exact message.modifyRejectedPresenceBits.property)]
  simp only [carried_modifyRejectedPresenceBits]
  rfl

end ModifyRejectedMessage

/-- Order Replaced Message -/
structure OrderReplacedMessage where
  orderReplacedPresenceBits : Masked 16 1023
  transactTime : BitVec 64
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  orderReplacedBitFields : BitVec 16
  leavesQty : BitVec 32
  orderReplacedPrice : Option (BitVec 64)
  orderReplacedOrderQty : Option (BitVec 32)
  orderReplacedMaxFloorQty : Option (BitVec 32)
  orderReplacedSelfMatchScope : Option (BitVec 8)
  orderReplacedSelfMatchInstruction : Option (BitVec 8)
  orderReplacedPriceSlideInstruction : Option (BitVec 8)
  orderReplacedReferencePriceTarget : Option (BitVec 16)
  orderReplacedLocateBroker : Option (Alpha 4)
  orderReplacedRankPrice : Option (BitVec 64)
  orderReplacedDisplayPrice : Option (BitVec 64)
  deriving DecidableEq, Repr

namespace OrderReplacedMessage

def encode (message : OrderReplacedMessage) : List UInt8 :=
  encodeUIntLE 2 (message.orderReplacedPresenceBits.val ||| presence (n := 16) 1 message.orderReplacedPrice.isSome ||| presence (n := 16) 2 message.orderReplacedOrderQty.isSome ||| presence (n := 16) 4 message.orderReplacedMaxFloorQty.isSome ||| presence (n := 16) 8 message.orderReplacedSelfMatchScope.isSome ||| presence (n := 16) 16 message.orderReplacedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.orderReplacedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.orderReplacedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.orderReplacedLocateBroker.isSome ||| presence (n := 16) 256 message.orderReplacedRankPrice.isSome ||| presence (n := 16) 512 message.orderReplacedDisplayPrice.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 2 message.orderReplacedBitFields
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeOptional (encodeUIntLE 8) message.orderReplacedPrice
    ++ (encodeOptional (encodeUIntLE 4) message.orderReplacedOrderQty
    ++ (encodeOptional (encodeUIntLE 4) message.orderReplacedMaxFloorQty
    ++ (encodeOptional (encodeUIntLE 1) message.orderReplacedSelfMatchScope
    ++ (encodeOptional (encodeUIntLE 1) message.orderReplacedSelfMatchInstruction
    ++ (encodeOptional (encodeUIntLE 1) message.orderReplacedPriceSlideInstruction
    ++ (encodeOptional (encodeUIntLE 2) message.orderReplacedReferencePriceTarget
    ++ (encodeOptional (Alpha.encode) message.orderReplacedLocateBroker
    ++ (encodeOptional (encodeUIntLE 8) message.orderReplacedRankPrice
    ++ (encodeOptional (encodeUIntLE 8) message.orderReplacedDisplayPrice))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderReplacedMessage × List UInt8) := do
  let (orderReplacedPresenceBits_, bytes) ← decodeUIntLE 2 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderReplacedBitFields, bytes) ← decodeUIntLE 2 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (orderReplacedPrice, bytes) ← decodeOptional (decodeUIntLE 8) (orderReplacedPresenceBits_ &&& 1 != 0) bytes
  let (orderReplacedOrderQty, bytes) ← decodeOptional (decodeUIntLE 4) (orderReplacedPresenceBits_ &&& 2 != 0) bytes
  let (orderReplacedMaxFloorQty, bytes) ← decodeOptional (decodeUIntLE 4) (orderReplacedPresenceBits_ &&& 4 != 0) bytes
  let (orderReplacedSelfMatchScope, bytes) ← decodeOptional (decodeUIntLE 1) (orderReplacedPresenceBits_ &&& 8 != 0) bytes
  let (orderReplacedSelfMatchInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (orderReplacedPresenceBits_ &&& 16 != 0) bytes
  let (orderReplacedPriceSlideInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (orderReplacedPresenceBits_ &&& 32 != 0) bytes
  let (orderReplacedReferencePriceTarget, bytes) ← decodeOptional (decodeUIntLE 2) (orderReplacedPresenceBits_ &&& 64 != 0) bytes
  let (orderReplacedLocateBroker, bytes) ← decodeOptional (Alpha.decode 4) (orderReplacedPresenceBits_ &&& 128 != 0) bytes
  let (orderReplacedRankPrice, bytes) ← decodeOptional (decodeUIntLE 8) (orderReplacedPresenceBits_ &&& 256 != 0) bytes
  let (orderReplacedDisplayPrice, bytes) ← decodeOptional (decodeUIntLE 8) (orderReplacedPresenceBits_ &&& 512 != 0) bytes
  if fits_orderReplacedPresenceBits : (orderReplacedPresenceBits_ &&& 64512) &&& 1023 = 0 then
    pure ({ orderReplacedPresenceBits := ⟨orderReplacedPresenceBits_ &&& 64512, fits_orderReplacedPresenceBits⟩, transactTime, orderId, clOrdId, origClOrdId, orderReplacedBitFields, leavesQty, orderReplacedPrice, orderReplacedOrderQty, orderReplacedMaxFloorQty, orderReplacedSelfMatchScope, orderReplacedSelfMatchInstruction, orderReplacedPriceSlideInstruction, orderReplacedReferencePriceTarget, orderReplacedLocateBroker, orderReplacedRankPrice, orderReplacedDisplayPrice }, bytes)
  else none

theorem encode_length_pos (message : OrderReplacedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : OrderReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_orderReplacedPrice : ((message.orderReplacedPresenceBits.val ||| presence (n := 16) 1 message.orderReplacedPrice.isSome ||| presence (n := 16) 2 message.orderReplacedOrderQty.isSome ||| presence (n := 16) 4 message.orderReplacedMaxFloorQty.isSome ||| presence (n := 16) 8 message.orderReplacedSelfMatchScope.isSome ||| presence (n := 16) 16 message.orderReplacedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.orderReplacedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.orderReplacedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.orderReplacedLocateBroker.isSome ||| presence (n := 16) 256 message.orderReplacedRankPrice.isSome ||| presence (n := 16) 512 message.orderReplacedDisplayPrice.isSome) &&& 1 != 0) = message.orderReplacedPrice.isSome := by
    have clear := message.orderReplacedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_orderReplacedOrderQty : ((message.orderReplacedPresenceBits.val ||| presence (n := 16) 1 message.orderReplacedPrice.isSome ||| presence (n := 16) 2 message.orderReplacedOrderQty.isSome ||| presence (n := 16) 4 message.orderReplacedMaxFloorQty.isSome ||| presence (n := 16) 8 message.orderReplacedSelfMatchScope.isSome ||| presence (n := 16) 16 message.orderReplacedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.orderReplacedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.orderReplacedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.orderReplacedLocateBroker.isSome ||| presence (n := 16) 256 message.orderReplacedRankPrice.isSome ||| presence (n := 16) 512 message.orderReplacedDisplayPrice.isSome) &&& 2 != 0) = message.orderReplacedOrderQty.isSome := by
    have clear := message.orderReplacedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_orderReplacedMaxFloorQty : ((message.orderReplacedPresenceBits.val ||| presence (n := 16) 1 message.orderReplacedPrice.isSome ||| presence (n := 16) 2 message.orderReplacedOrderQty.isSome ||| presence (n := 16) 4 message.orderReplacedMaxFloorQty.isSome ||| presence (n := 16) 8 message.orderReplacedSelfMatchScope.isSome ||| presence (n := 16) 16 message.orderReplacedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.orderReplacedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.orderReplacedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.orderReplacedLocateBroker.isSome ||| presence (n := 16) 256 message.orderReplacedRankPrice.isSome ||| presence (n := 16) 512 message.orderReplacedDisplayPrice.isSome) &&& 4 != 0) = message.orderReplacedMaxFloorQty.isSome := by
    have clear := message.orderReplacedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_orderReplacedSelfMatchScope : ((message.orderReplacedPresenceBits.val ||| presence (n := 16) 1 message.orderReplacedPrice.isSome ||| presence (n := 16) 2 message.orderReplacedOrderQty.isSome ||| presence (n := 16) 4 message.orderReplacedMaxFloorQty.isSome ||| presence (n := 16) 8 message.orderReplacedSelfMatchScope.isSome ||| presence (n := 16) 16 message.orderReplacedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.orderReplacedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.orderReplacedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.orderReplacedLocateBroker.isSome ||| presence (n := 16) 256 message.orderReplacedRankPrice.isSome ||| presence (n := 16) 512 message.orderReplacedDisplayPrice.isSome) &&& 8 != 0) = message.orderReplacedSelfMatchScope.isSome := by
    have clear := message.orderReplacedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_orderReplacedSelfMatchInstruction : ((message.orderReplacedPresenceBits.val ||| presence (n := 16) 1 message.orderReplacedPrice.isSome ||| presence (n := 16) 2 message.orderReplacedOrderQty.isSome ||| presence (n := 16) 4 message.orderReplacedMaxFloorQty.isSome ||| presence (n := 16) 8 message.orderReplacedSelfMatchScope.isSome ||| presence (n := 16) 16 message.orderReplacedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.orderReplacedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.orderReplacedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.orderReplacedLocateBroker.isSome ||| presence (n := 16) 256 message.orderReplacedRankPrice.isSome ||| presence (n := 16) 512 message.orderReplacedDisplayPrice.isSome) &&& 16 != 0) = message.orderReplacedSelfMatchInstruction.isSome := by
    have clear := message.orderReplacedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_orderReplacedPriceSlideInstruction : ((message.orderReplacedPresenceBits.val ||| presence (n := 16) 1 message.orderReplacedPrice.isSome ||| presence (n := 16) 2 message.orderReplacedOrderQty.isSome ||| presence (n := 16) 4 message.orderReplacedMaxFloorQty.isSome ||| presence (n := 16) 8 message.orderReplacedSelfMatchScope.isSome ||| presence (n := 16) 16 message.orderReplacedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.orderReplacedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.orderReplacedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.orderReplacedLocateBroker.isSome ||| presence (n := 16) 256 message.orderReplacedRankPrice.isSome ||| presence (n := 16) 512 message.orderReplacedDisplayPrice.isSome) &&& 32 != 0) = message.orderReplacedPriceSlideInstruction.isSome := by
    have clear := message.orderReplacedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_orderReplacedReferencePriceTarget : ((message.orderReplacedPresenceBits.val ||| presence (n := 16) 1 message.orderReplacedPrice.isSome ||| presence (n := 16) 2 message.orderReplacedOrderQty.isSome ||| presence (n := 16) 4 message.orderReplacedMaxFloorQty.isSome ||| presence (n := 16) 8 message.orderReplacedSelfMatchScope.isSome ||| presence (n := 16) 16 message.orderReplacedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.orderReplacedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.orderReplacedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.orderReplacedLocateBroker.isSome ||| presence (n := 16) 256 message.orderReplacedRankPrice.isSome ||| presence (n := 16) 512 message.orderReplacedDisplayPrice.isSome) &&& 64 != 0) = message.orderReplacedReferencePriceTarget.isSome := by
    have clear := message.orderReplacedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_orderReplacedLocateBroker : ((message.orderReplacedPresenceBits.val ||| presence (n := 16) 1 message.orderReplacedPrice.isSome ||| presence (n := 16) 2 message.orderReplacedOrderQty.isSome ||| presence (n := 16) 4 message.orderReplacedMaxFloorQty.isSome ||| presence (n := 16) 8 message.orderReplacedSelfMatchScope.isSome ||| presence (n := 16) 16 message.orderReplacedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.orderReplacedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.orderReplacedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.orderReplacedLocateBroker.isSome ||| presence (n := 16) 256 message.orderReplacedRankPrice.isSome ||| presence (n := 16) 512 message.orderReplacedDisplayPrice.isSome) &&& 128 != 0) = message.orderReplacedLocateBroker.isSome := by
    have clear := message.orderReplacedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_orderReplacedRankPrice : ((message.orderReplacedPresenceBits.val ||| presence (n := 16) 1 message.orderReplacedPrice.isSome ||| presence (n := 16) 2 message.orderReplacedOrderQty.isSome ||| presence (n := 16) 4 message.orderReplacedMaxFloorQty.isSome ||| presence (n := 16) 8 message.orderReplacedSelfMatchScope.isSome ||| presence (n := 16) 16 message.orderReplacedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.orderReplacedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.orderReplacedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.orderReplacedLocateBroker.isSome ||| presence (n := 16) 256 message.orderReplacedRankPrice.isSome ||| presence (n := 16) 512 message.orderReplacedDisplayPrice.isSome) &&& 256 != 0) = message.orderReplacedRankPrice.isSome := by
    have clear := message.orderReplacedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_orderReplacedDisplayPrice : ((message.orderReplacedPresenceBits.val ||| presence (n := 16) 1 message.orderReplacedPrice.isSome ||| presence (n := 16) 2 message.orderReplacedOrderQty.isSome ||| presence (n := 16) 4 message.orderReplacedMaxFloorQty.isSome ||| presence (n := 16) 8 message.orderReplacedSelfMatchScope.isSome ||| presence (n := 16) 16 message.orderReplacedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.orderReplacedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.orderReplacedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.orderReplacedLocateBroker.isSome ||| presence (n := 16) 256 message.orderReplacedRankPrice.isSome ||| presence (n := 16) 512 message.orderReplacedDisplayPrice.isSome) &&& 512 != 0) = message.orderReplacedDisplayPrice.isSome := by
    have clear := message.orderReplacedPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_orderReplacedPresenceBits : (message.orderReplacedPresenceBits.val ||| presence (n := 16) 1 message.orderReplacedPrice.isSome ||| presence (n := 16) 2 message.orderReplacedOrderQty.isSome ||| presence (n := 16) 4 message.orderReplacedMaxFloorQty.isSome ||| presence (n := 16) 8 message.orderReplacedSelfMatchScope.isSome ||| presence (n := 16) 16 message.orderReplacedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.orderReplacedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.orderReplacedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.orderReplacedLocateBroker.isSome ||| presence (n := 16) 256 message.orderReplacedRankPrice.isSome ||| presence (n := 16) 512 message.orderReplacedDisplayPrice.isSome) &&& 64512 = message.orderReplacedPresenceBits.val := by
    have clear := message.orderReplacedPresenceBits.property
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_orderReplacedPrice]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_orderReplacedOrderQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_orderReplacedMaxFloorQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_orderReplacedSelfMatchScope]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_orderReplacedSelfMatchInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_orderReplacedPriceSlideInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_orderReplacedReferencePriceTarget]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 2) (decodeUIntLE 2) (decodeUIntLE_encodeUIntLE 2), some_bind]
  dsimp only
  rw [selected_orderReplacedLocateBroker]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_orderReplacedRankPrice]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_orderReplacedDisplayPrice]
  rw [decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_orderReplacedPresenceBits]; exact message.orderReplacedPresenceBits.property)]
  simp only [carried_orderReplacedPresenceBits]
  rfl

end OrderReplacedMessage

/-- Replace Rejected Message -/
structure ReplaceRejectedMessage where
  replaceRejectedPresenceBits : Masked 16 255
  transactTime : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  replaceRejectedBitFields : BitVec 16
  replaceRejectedReason : BitVec 8
  replaceRejectedPrice : Option (BitVec 64)
  replaceRejectedOrderQty : Option (BitVec 32)
  replaceRejectedMaxFloorQty : Option (BitVec 32)
  replaceRejectedSelfMatchScope : Option (BitVec 8)
  replaceRejectedSelfMatchInstruction : Option (BitVec 8)
  replaceRejectedPriceSlideInstruction : Option (BitVec 8)
  replaceRejectedReferencePriceTarget : Option (BitVec 16)
  replaceRejectedLocateBroker : Option (Alpha 4)
  deriving DecidableEq, Repr

namespace ReplaceRejectedMessage

def encode (message : ReplaceRejectedMessage) : List UInt8 :=
  encodeUIntLE 2 (message.replaceRejectedPresenceBits.val ||| presence (n := 16) 1 message.replaceRejectedPrice.isSome ||| presence (n := 16) 2 message.replaceRejectedOrderQty.isSome ||| presence (n := 16) 4 message.replaceRejectedMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceRejectedSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceRejectedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceRejectedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceRejectedLocateBroker.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 2 message.replaceRejectedBitFields
    ++ (encodeUIntLE 1 message.replaceRejectedReason
    ++ (encodeOptional (encodeUIntLE 8) message.replaceRejectedPrice
    ++ (encodeOptional (encodeUIntLE 4) message.replaceRejectedOrderQty
    ++ (encodeOptional (encodeUIntLE 4) message.replaceRejectedMaxFloorQty
    ++ (encodeOptional (encodeUIntLE 1) message.replaceRejectedSelfMatchScope
    ++ (encodeOptional (encodeUIntLE 1) message.replaceRejectedSelfMatchInstruction
    ++ (encodeOptional (encodeUIntLE 1) message.replaceRejectedPriceSlideInstruction
    ++ (encodeOptional (encodeUIntLE 2) message.replaceRejectedReferencePriceTarget
    ++ (encodeOptional (Alpha.encode) message.replaceRejectedLocateBroker)))))))))))))

def decode (bytes : List UInt8) : Option (ReplaceRejectedMessage × List UInt8) := do
  let (replaceRejectedPresenceBits_, bytes) ← decodeUIntLE 2 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (replaceRejectedBitFields, bytes) ← decodeUIntLE 2 bytes
  let (replaceRejectedReason, bytes) ← decodeUIntLE 1 bytes
  let (replaceRejectedPrice, bytes) ← decodeOptional (decodeUIntLE 8) (replaceRejectedPresenceBits_ &&& 1 != 0) bytes
  let (replaceRejectedOrderQty, bytes) ← decodeOptional (decodeUIntLE 4) (replaceRejectedPresenceBits_ &&& 2 != 0) bytes
  let (replaceRejectedMaxFloorQty, bytes) ← decodeOptional (decodeUIntLE 4) (replaceRejectedPresenceBits_ &&& 4 != 0) bytes
  let (replaceRejectedSelfMatchScope, bytes) ← decodeOptional (decodeUIntLE 1) (replaceRejectedPresenceBits_ &&& 8 != 0) bytes
  let (replaceRejectedSelfMatchInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (replaceRejectedPresenceBits_ &&& 16 != 0) bytes
  let (replaceRejectedPriceSlideInstruction, bytes) ← decodeOptional (decodeUIntLE 1) (replaceRejectedPresenceBits_ &&& 32 != 0) bytes
  let (replaceRejectedReferencePriceTarget, bytes) ← decodeOptional (decodeUIntLE 2) (replaceRejectedPresenceBits_ &&& 64 != 0) bytes
  let (replaceRejectedLocateBroker, bytes) ← decodeOptional (Alpha.decode 4) (replaceRejectedPresenceBits_ &&& 128 != 0) bytes
  if fits_replaceRejectedPresenceBits : (replaceRejectedPresenceBits_ &&& 65280) &&& 255 = 0 then
    pure ({ replaceRejectedPresenceBits := ⟨replaceRejectedPresenceBits_ &&& 65280, fits_replaceRejectedPresenceBits⟩, transactTime, clOrdId, origClOrdId, replaceRejectedBitFields, replaceRejectedReason, replaceRejectedPrice, replaceRejectedOrderQty, replaceRejectedMaxFloorQty, replaceRejectedSelfMatchScope, replaceRejectedSelfMatchInstruction, replaceRejectedPriceSlideInstruction, replaceRejectedReferencePriceTarget, replaceRejectedLocateBroker }, bytes)
  else none

theorem encode_length_pos (message : ReplaceRejectedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : ReplaceRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_replaceRejectedPrice : ((message.replaceRejectedPresenceBits.val ||| presence (n := 16) 1 message.replaceRejectedPrice.isSome ||| presence (n := 16) 2 message.replaceRejectedOrderQty.isSome ||| presence (n := 16) 4 message.replaceRejectedMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceRejectedSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceRejectedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceRejectedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceRejectedLocateBroker.isSome) &&& 1 != 0) = message.replaceRejectedPrice.isSome := by
    have clear := message.replaceRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceRejectedOrderQty : ((message.replaceRejectedPresenceBits.val ||| presence (n := 16) 1 message.replaceRejectedPrice.isSome ||| presence (n := 16) 2 message.replaceRejectedOrderQty.isSome ||| presence (n := 16) 4 message.replaceRejectedMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceRejectedSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceRejectedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceRejectedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceRejectedLocateBroker.isSome) &&& 2 != 0) = message.replaceRejectedOrderQty.isSome := by
    have clear := message.replaceRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceRejectedMaxFloorQty : ((message.replaceRejectedPresenceBits.val ||| presence (n := 16) 1 message.replaceRejectedPrice.isSome ||| presence (n := 16) 2 message.replaceRejectedOrderQty.isSome ||| presence (n := 16) 4 message.replaceRejectedMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceRejectedSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceRejectedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceRejectedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceRejectedLocateBroker.isSome) &&& 4 != 0) = message.replaceRejectedMaxFloorQty.isSome := by
    have clear := message.replaceRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceRejectedSelfMatchScope : ((message.replaceRejectedPresenceBits.val ||| presence (n := 16) 1 message.replaceRejectedPrice.isSome ||| presence (n := 16) 2 message.replaceRejectedOrderQty.isSome ||| presence (n := 16) 4 message.replaceRejectedMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceRejectedSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceRejectedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceRejectedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceRejectedLocateBroker.isSome) &&& 8 != 0) = message.replaceRejectedSelfMatchScope.isSome := by
    have clear := message.replaceRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceRejectedSelfMatchInstruction : ((message.replaceRejectedPresenceBits.val ||| presence (n := 16) 1 message.replaceRejectedPrice.isSome ||| presence (n := 16) 2 message.replaceRejectedOrderQty.isSome ||| presence (n := 16) 4 message.replaceRejectedMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceRejectedSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceRejectedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceRejectedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceRejectedLocateBroker.isSome) &&& 16 != 0) = message.replaceRejectedSelfMatchInstruction.isSome := by
    have clear := message.replaceRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceRejectedPriceSlideInstruction : ((message.replaceRejectedPresenceBits.val ||| presence (n := 16) 1 message.replaceRejectedPrice.isSome ||| presence (n := 16) 2 message.replaceRejectedOrderQty.isSome ||| presence (n := 16) 4 message.replaceRejectedMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceRejectedSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceRejectedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceRejectedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceRejectedLocateBroker.isSome) &&& 32 != 0) = message.replaceRejectedPriceSlideInstruction.isSome := by
    have clear := message.replaceRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceRejectedReferencePriceTarget : ((message.replaceRejectedPresenceBits.val ||| presence (n := 16) 1 message.replaceRejectedPrice.isSome ||| presence (n := 16) 2 message.replaceRejectedOrderQty.isSome ||| presence (n := 16) 4 message.replaceRejectedMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceRejectedSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceRejectedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceRejectedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceRejectedLocateBroker.isSome) &&& 64 != 0) = message.replaceRejectedReferencePriceTarget.isSome := by
    have clear := message.replaceRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_replaceRejectedLocateBroker : ((message.replaceRejectedPresenceBits.val ||| presence (n := 16) 1 message.replaceRejectedPrice.isSome ||| presence (n := 16) 2 message.replaceRejectedOrderQty.isSome ||| presence (n := 16) 4 message.replaceRejectedMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceRejectedSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceRejectedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceRejectedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceRejectedLocateBroker.isSome) &&& 128 != 0) = message.replaceRejectedLocateBroker.isSome := by
    have clear := message.replaceRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_replaceRejectedPresenceBits : (message.replaceRejectedPresenceBits.val ||| presence (n := 16) 1 message.replaceRejectedPrice.isSome ||| presence (n := 16) 2 message.replaceRejectedOrderQty.isSome ||| presence (n := 16) 4 message.replaceRejectedMaxFloorQty.isSome ||| presence (n := 16) 8 message.replaceRejectedSelfMatchScope.isSome ||| presence (n := 16) 16 message.replaceRejectedSelfMatchInstruction.isSome ||| presence (n := 16) 32 message.replaceRejectedPriceSlideInstruction.isSome ||| presence (n := 16) 64 message.replaceRejectedReferencePriceTarget.isSome ||| presence (n := 16) 128 message.replaceRejectedLocateBroker.isSome) &&& 65280 = message.replaceRejectedPresenceBits.val := by
    have clear := message.replaceRejectedPresenceBits.property
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
  rw [selected_replaceRejectedPrice]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_replaceRejectedOrderQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_replaceRejectedMaxFloorQty]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [selected_replaceRejectedSelfMatchScope]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_replaceRejectedSelfMatchInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_replaceRejectedPriceSlideInstruction]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_replaceRejectedReferencePriceTarget]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 2) (decodeUIntLE 2) (decodeUIntLE_encodeUIntLE 2), some_bind]
  dsimp only
  rw [selected_replaceRejectedLocateBroker]
  rw [decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_replaceRejectedPresenceBits]; exact message.replaceRejectedPresenceBits.property)]
  simp only [carried_replaceRejectedPresenceBits]
  rfl

end ReplaceRejectedMessage

/-- Order Executed Message: 49 bytes -/
structure OrderExecutedMessage where
  transactTime : BitVec 64
  orderId : BitVec 64
  clOrdId : BitVec 64
  execPrice : BitVec 64
  execId : BitVec 64
  execQty : BitVec 32
  leavesQty : BitVec 32
  liquidityIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.execPrice
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 4 message.execQty
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 1 message.liquidityIndicator)))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (execPrice, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (execQty, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (liquidityIndicator, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, orderId, clOrdId, execPrice, execId, execQty, leavesQty, liquidityIndicator }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Restated Message -/
structure OrderRestatedMessage where
  orderRestatedPresenceBits : Masked 8 7
  transactTime : BitVec 64
  orderId : BitVec 64
  clOrdId : BitVec 64
  restatementReason : BitVec 8
  orderRestatedRankPrice : Option (BitVec 64)
  orderRestatedDisplayPrice : Option (BitVec 64)
  displayQty : Option (BitVec 32)
  deriving DecidableEq, Repr

namespace OrderRestatedMessage

def encode (message : OrderRestatedMessage) : List UInt8 :=
  encodeUIntLE 1 (message.orderRestatedPresenceBits.val ||| presence (n := 8) 1 message.orderRestatedRankPrice.isSome ||| presence (n := 8) 2 message.orderRestatedDisplayPrice.isSome ||| presence (n := 8) 4 message.displayQty.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 1 message.restatementReason
    ++ (encodeOptional (encodeUIntLE 8) message.orderRestatedRankPrice
    ++ (encodeOptional (encodeUIntLE 8) message.orderRestatedDisplayPrice
    ++ (encodeOptional (encodeUIntLE 4) message.displayQty)))))))

def decode (bytes : List UInt8) : Option (OrderRestatedMessage × List UInt8) := do
  let (orderRestatedPresenceBits_, bytes) ← decodeUIntLE 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (restatementReason, bytes) ← decodeUIntLE 1 bytes
  let (orderRestatedRankPrice, bytes) ← decodeOptional (decodeUIntLE 8) (orderRestatedPresenceBits_ &&& 1 != 0) bytes
  let (orderRestatedDisplayPrice, bytes) ← decodeOptional (decodeUIntLE 8) (orderRestatedPresenceBits_ &&& 2 != 0) bytes
  let (displayQty, bytes) ← decodeOptional (decodeUIntLE 4) (orderRestatedPresenceBits_ &&& 4 != 0) bytes
  if fits_orderRestatedPresenceBits : (orderRestatedPresenceBits_ &&& 248) &&& 7 = 0 then
    pure ({ orderRestatedPresenceBits := ⟨orderRestatedPresenceBits_ &&& 248, fits_orderRestatedPresenceBits⟩, transactTime, orderId, clOrdId, restatementReason, orderRestatedRankPrice, orderRestatedDisplayPrice, displayQty }, bytes)
  else none

theorem encode_length_pos (message : OrderRestatedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : OrderRestatedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_orderRestatedRankPrice : ((message.orderRestatedPresenceBits.val ||| presence (n := 8) 1 message.orderRestatedRankPrice.isSome ||| presence (n := 8) 2 message.orderRestatedDisplayPrice.isSome ||| presence (n := 8) 4 message.displayQty.isSome) &&& 1 != 0) = message.orderRestatedRankPrice.isSome := by
    have clear := message.orderRestatedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_orderRestatedDisplayPrice : ((message.orderRestatedPresenceBits.val ||| presence (n := 8) 1 message.orderRestatedRankPrice.isSome ||| presence (n := 8) 2 message.orderRestatedDisplayPrice.isSome ||| presence (n := 8) 4 message.displayQty.isSome) &&& 2 != 0) = message.orderRestatedDisplayPrice.isSome := by
    have clear := message.orderRestatedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_displayQty : ((message.orderRestatedPresenceBits.val ||| presence (n := 8) 1 message.orderRestatedRankPrice.isSome ||| presence (n := 8) 2 message.orderRestatedDisplayPrice.isSome ||| presence (n := 8) 4 message.displayQty.isSome) &&& 4 != 0) = message.displayQty.isSome := by
    have clear := message.orderRestatedPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_orderRestatedPresenceBits : (message.orderRestatedPresenceBits.val ||| presence (n := 8) 1 message.orderRestatedRankPrice.isSome ||| presence (n := 8) 2 message.orderRestatedDisplayPrice.isSome ||| presence (n := 8) 4 message.displayQty.isSome) &&& 248 = message.orderRestatedPresenceBits.val := by
    have clear := message.orderRestatedPresenceBits.property
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
  rw [selected_orderRestatedRankPrice]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_orderRestatedDisplayPrice]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [selected_displayQty]
  rw [decodeOptional_encodeOptional (encodeUIntLE 4) (decodeUIntLE 4) (decodeUIntLE_encodeUIntLE 4), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_orderRestatedPresenceBits]; exact message.orderRestatedPresenceBits.property)]
  simp only [carried_orderRestatedPresenceBits]
  rfl

end OrderRestatedMessage

/-- Self Match Prevented Message: 53 bytes -/
structure SelfMatchPreventedMessage where
  transactTime : BitVec 64
  orderId : BitVec 64
  clOrdId : BitVec 64
  execPrice : BitVec 64
  execId : BitVec 64
  execQty : BitVec 32
  canceledQty : BitVec 32
  leavesQty : BitVec 32
  liquidityIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace SelfMatchPreventedMessage

def encode (message : SelfMatchPreventedMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.execPrice
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 4 message.execQty
    ++ (encodeUIntLE 4 message.canceledQty
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 1 message.liquidityIndicator))))))))

def decode (bytes : List UInt8) : Option (SelfMatchPreventedMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (execPrice, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (execQty, bytes) ← decodeUIntLE 4 bytes
  let (canceledQty, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (liquidityIndicator, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, orderId, clOrdId, execPrice, execId, execQty, canceledQty, leavesQty, liquidityIndicator }, bytes)

@[simp] theorem encode_length (message : SelfMatchPreventedMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SelfMatchPreventedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SelfMatchPreventedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SelfMatchPreventedMessage

/-- Mass Cancel Accepted Message -/
structure MassCancelAcceptedMessage where
  massCancelAcceptedPresenceBits : Masked 8 15
  transactTime : BitVec 64
  massCancelRequestId : BitVec 64
  massCancelAcceptedScope : BitVec 8
  massCancelAcceptedBitFields : BitVec 8
  massCancelId : BitVec 64
  massCancelAcceptedMpid : Option (Alpha 4)
  massCancelAcceptedSenderComp : Option (Alpha 8)
  massCancelAcceptedMemberGroup : Option (Alpha 2)
  massCancelAcceptedClOrdId : Option (BitVec 64)
  deriving DecidableEq, Repr

namespace MassCancelAcceptedMessage

def encode (message : MassCancelAcceptedMessage) : List UInt8 :=
  encodeUIntLE 1 (message.massCancelAcceptedPresenceBits.val ||| presence (n := 8) 1 message.massCancelAcceptedMpid.isSome ||| presence (n := 8) 2 message.massCancelAcceptedSenderComp.isSome ||| presence (n := 8) 4 message.massCancelAcceptedMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelAcceptedClOrdId.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.massCancelRequestId
    ++ (encodeUIntLE 1 message.massCancelAcceptedScope
    ++ (encodeUIntLE 1 message.massCancelAcceptedBitFields
    ++ (encodeUIntLE 8 message.massCancelId
    ++ (encodeOptional (Alpha.encode) message.massCancelAcceptedMpid
    ++ (encodeOptional (Alpha.encode) message.massCancelAcceptedSenderComp
    ++ (encodeOptional (Alpha.encode) message.massCancelAcceptedMemberGroup
    ++ (encodeOptional (encodeUIntLE 8) message.massCancelAcceptedClOrdId)))))))))

def decode (bytes : List UInt8) : Option (MassCancelAcceptedMessage × List UInt8) := do
  let (massCancelAcceptedPresenceBits_, bytes) ← decodeUIntLE 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (massCancelRequestId, bytes) ← decodeUIntLE 8 bytes
  let (massCancelAcceptedScope, bytes) ← decodeUIntLE 1 bytes
  let (massCancelAcceptedBitFields, bytes) ← decodeUIntLE 1 bytes
  let (massCancelId, bytes) ← decodeUIntLE 8 bytes
  let (massCancelAcceptedMpid, bytes) ← decodeOptional (Alpha.decode 4) (massCancelAcceptedPresenceBits_ &&& 1 != 0) bytes
  let (massCancelAcceptedSenderComp, bytes) ← decodeOptional (Alpha.decode 8) (massCancelAcceptedPresenceBits_ &&& 2 != 0) bytes
  let (massCancelAcceptedMemberGroup, bytes) ← decodeOptional (Alpha.decode 2) (massCancelAcceptedPresenceBits_ &&& 4 != 0) bytes
  let (massCancelAcceptedClOrdId, bytes) ← decodeOptional (decodeUIntLE 8) (massCancelAcceptedPresenceBits_ &&& 8 != 0) bytes
  if fits_massCancelAcceptedPresenceBits : (massCancelAcceptedPresenceBits_ &&& 240) &&& 15 = 0 then
    pure ({ massCancelAcceptedPresenceBits := ⟨massCancelAcceptedPresenceBits_ &&& 240, fits_massCancelAcceptedPresenceBits⟩, transactTime, massCancelRequestId, massCancelAcceptedScope, massCancelAcceptedBitFields, massCancelId, massCancelAcceptedMpid, massCancelAcceptedSenderComp, massCancelAcceptedMemberGroup, massCancelAcceptedClOrdId }, bytes)
  else none

theorem encode_length_pos (message : MassCancelAcceptedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : MassCancelAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_massCancelAcceptedMpid : ((message.massCancelAcceptedPresenceBits.val ||| presence (n := 8) 1 message.massCancelAcceptedMpid.isSome ||| presence (n := 8) 2 message.massCancelAcceptedSenderComp.isSome ||| presence (n := 8) 4 message.massCancelAcceptedMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelAcceptedClOrdId.isSome) &&& 1 != 0) = message.massCancelAcceptedMpid.isSome := by
    have clear := message.massCancelAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_massCancelAcceptedSenderComp : ((message.massCancelAcceptedPresenceBits.val ||| presence (n := 8) 1 message.massCancelAcceptedMpid.isSome ||| presence (n := 8) 2 message.massCancelAcceptedSenderComp.isSome ||| presence (n := 8) 4 message.massCancelAcceptedMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelAcceptedClOrdId.isSome) &&& 2 != 0) = message.massCancelAcceptedSenderComp.isSome := by
    have clear := message.massCancelAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_massCancelAcceptedMemberGroup : ((message.massCancelAcceptedPresenceBits.val ||| presence (n := 8) 1 message.massCancelAcceptedMpid.isSome ||| presence (n := 8) 2 message.massCancelAcceptedSenderComp.isSome ||| presence (n := 8) 4 message.massCancelAcceptedMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelAcceptedClOrdId.isSome) &&& 4 != 0) = message.massCancelAcceptedMemberGroup.isSome := by
    have clear := message.massCancelAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_massCancelAcceptedClOrdId : ((message.massCancelAcceptedPresenceBits.val ||| presence (n := 8) 1 message.massCancelAcceptedMpid.isSome ||| presence (n := 8) 2 message.massCancelAcceptedSenderComp.isSome ||| presence (n := 8) 4 message.massCancelAcceptedMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelAcceptedClOrdId.isSome) &&& 8 != 0) = message.massCancelAcceptedClOrdId.isSome := by
    have clear := message.massCancelAcceptedPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_massCancelAcceptedPresenceBits : (message.massCancelAcceptedPresenceBits.val ||| presence (n := 8) 1 message.massCancelAcceptedMpid.isSome ||| presence (n := 8) 2 message.massCancelAcceptedSenderComp.isSome ||| presence (n := 8) 4 message.massCancelAcceptedMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelAcceptedClOrdId.isSome) &&& 240 = message.massCancelAcceptedPresenceBits.val := by
    have clear := message.massCancelAcceptedPresenceBits.property
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
  rw [selected_massCancelAcceptedMpid]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_massCancelAcceptedSenderComp]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 8) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_massCancelAcceptedMemberGroup]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 2) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_massCancelAcceptedClOrdId]
  rw [decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_massCancelAcceptedPresenceBits]; exact message.massCancelAcceptedPresenceBits.property)]
  simp only [carried_massCancelAcceptedPresenceBits]
  rfl

end MassCancelAcceptedMessage

/-- Mass Cancel Rejected Message -/
structure MassCancelRejectedMessage where
  massCancelRejectedPresenceBits : Masked 8 15
  transactTime : BitVec 64
  massCancelRequestId : BitVec 64
  massCancelRejectedScope : BitVec 8
  massCancelRejectedBitFields : BitVec 8
  massCancelRejectedReason : BitVec 8
  massCancelRejectedMpid : Option (Alpha 4)
  massCancelRejectedSenderComp : Option (Alpha 8)
  massCancelRejectedMemberGroup : Option (Alpha 2)
  massCancelRejectedClOrdId : Option (BitVec 64)
  deriving DecidableEq, Repr

namespace MassCancelRejectedMessage

def encode (message : MassCancelRejectedMessage) : List UInt8 :=
  encodeUIntLE 1 (message.massCancelRejectedPresenceBits.val ||| presence (n := 8) 1 message.massCancelRejectedMpid.isSome ||| presence (n := 8) 2 message.massCancelRejectedSenderComp.isSome ||| presence (n := 8) 4 message.massCancelRejectedMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelRejectedClOrdId.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.massCancelRequestId
    ++ (encodeUIntLE 1 message.massCancelRejectedScope
    ++ (encodeUIntLE 1 message.massCancelRejectedBitFields
    ++ (encodeUIntLE 1 message.massCancelRejectedReason
    ++ (encodeOptional (Alpha.encode) message.massCancelRejectedMpid
    ++ (encodeOptional (Alpha.encode) message.massCancelRejectedSenderComp
    ++ (encodeOptional (Alpha.encode) message.massCancelRejectedMemberGroup
    ++ (encodeOptional (encodeUIntLE 8) message.massCancelRejectedClOrdId)))))))))

def decode (bytes : List UInt8) : Option (MassCancelRejectedMessage × List UInt8) := do
  let (massCancelRejectedPresenceBits_, bytes) ← decodeUIntLE 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (massCancelRequestId, bytes) ← decodeUIntLE 8 bytes
  let (massCancelRejectedScope, bytes) ← decodeUIntLE 1 bytes
  let (massCancelRejectedBitFields, bytes) ← decodeUIntLE 1 bytes
  let (massCancelRejectedReason, bytes) ← decodeUIntLE 1 bytes
  let (massCancelRejectedMpid, bytes) ← decodeOptional (Alpha.decode 4) (massCancelRejectedPresenceBits_ &&& 1 != 0) bytes
  let (massCancelRejectedSenderComp, bytes) ← decodeOptional (Alpha.decode 8) (massCancelRejectedPresenceBits_ &&& 2 != 0) bytes
  let (massCancelRejectedMemberGroup, bytes) ← decodeOptional (Alpha.decode 2) (massCancelRejectedPresenceBits_ &&& 4 != 0) bytes
  let (massCancelRejectedClOrdId, bytes) ← decodeOptional (decodeUIntLE 8) (massCancelRejectedPresenceBits_ &&& 8 != 0) bytes
  if fits_massCancelRejectedPresenceBits : (massCancelRejectedPresenceBits_ &&& 240) &&& 15 = 0 then
    pure ({ massCancelRejectedPresenceBits := ⟨massCancelRejectedPresenceBits_ &&& 240, fits_massCancelRejectedPresenceBits⟩, transactTime, massCancelRequestId, massCancelRejectedScope, massCancelRejectedBitFields, massCancelRejectedReason, massCancelRejectedMpid, massCancelRejectedSenderComp, massCancelRejectedMemberGroup, massCancelRejectedClOrdId }, bytes)
  else none

theorem encode_length_pos (message : MassCancelRejectedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : MassCancelRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_massCancelRejectedMpid : ((message.massCancelRejectedPresenceBits.val ||| presence (n := 8) 1 message.massCancelRejectedMpid.isSome ||| presence (n := 8) 2 message.massCancelRejectedSenderComp.isSome ||| presence (n := 8) 4 message.massCancelRejectedMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelRejectedClOrdId.isSome) &&& 1 != 0) = message.massCancelRejectedMpid.isSome := by
    have clear := message.massCancelRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_massCancelRejectedSenderComp : ((message.massCancelRejectedPresenceBits.val ||| presence (n := 8) 1 message.massCancelRejectedMpid.isSome ||| presence (n := 8) 2 message.massCancelRejectedSenderComp.isSome ||| presence (n := 8) 4 message.massCancelRejectedMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelRejectedClOrdId.isSome) &&& 2 != 0) = message.massCancelRejectedSenderComp.isSome := by
    have clear := message.massCancelRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_massCancelRejectedMemberGroup : ((message.massCancelRejectedPresenceBits.val ||| presence (n := 8) 1 message.massCancelRejectedMpid.isSome ||| presence (n := 8) 2 message.massCancelRejectedSenderComp.isSome ||| presence (n := 8) 4 message.massCancelRejectedMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelRejectedClOrdId.isSome) &&& 4 != 0) = message.massCancelRejectedMemberGroup.isSome := by
    have clear := message.massCancelRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_massCancelRejectedClOrdId : ((message.massCancelRejectedPresenceBits.val ||| presence (n := 8) 1 message.massCancelRejectedMpid.isSome ||| presence (n := 8) 2 message.massCancelRejectedSenderComp.isSome ||| presence (n := 8) 4 message.massCancelRejectedMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelRejectedClOrdId.isSome) &&& 8 != 0) = message.massCancelRejectedClOrdId.isSome := by
    have clear := message.massCancelRejectedPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_massCancelRejectedPresenceBits : (message.massCancelRejectedPresenceBits.val ||| presence (n := 8) 1 message.massCancelRejectedMpid.isSome ||| presence (n := 8) 2 message.massCancelRejectedSenderComp.isSome ||| presence (n := 8) 4 message.massCancelRejectedMemberGroup.isSome ||| presence (n := 8) 8 message.massCancelRejectedClOrdId.isSome) &&& 240 = message.massCancelRejectedPresenceBits.val := by
    have clear := message.massCancelRejectedPresenceBits.property
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
  rw [selected_massCancelRejectedMpid]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 4) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_massCancelRejectedSenderComp]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 8) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_massCancelRejectedMemberGroup]
  rw [List.append_assoc, decodeOptional_encodeOptional (Alpha.encode) (Alpha.decode 2) (Alpha.decode_encode), some_bind]
  dsimp only
  rw [selected_massCancelRejectedClOrdId]
  rw [decodeOptional_encodeOptional (encodeUIntLE 8) (decodeUIntLE 8) (decodeUIntLE_encodeUIntLE 8), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_massCancelRejectedPresenceBits]; exact message.massCancelRejectedPresenceBits.property)]
  simp only [carried_massCancelRejectedPresenceBits]
  rfl

end MassCancelRejectedMessage

/-- Mass Cancel Result Message: 28 bytes -/
structure MassCancelResultMessage where
  transactTime : BitVec 64
  massCancelRequestId : BitVec 64
  massCancelId : BitVec 64
  canceledCount : BitVec 32
  deriving DecidableEq, Repr

namespace MassCancelResultMessage

def encode (message : MassCancelResultMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.massCancelRequestId
    ++ (encodeUIntLE 8 message.massCancelId
    ++ (encodeUIntLE 4 message.canceledCount)))

def decode (bytes : List UInt8) : Option (MassCancelResultMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (massCancelRequestId, bytes) ← decodeUIntLE 8 bytes
  let (massCancelId, bytes) ← decodeUIntLE 8 bytes
  let (canceledCount, bytes) ← decodeUIntLE 4 bytes
  pure ({ transactTime, massCancelRequestId, massCancelId, canceledCount }, bytes)

@[simp] theorem encode_length (message : MassCancelResultMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MassCancelResultMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelResultMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MassCancelResultMessage

/-- Any Sequenced Message, selected by Message Type -/
inductive SequencedMessage where
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 105
  | defineSymbolMessage (message : DefineSymbolMessage) -- 115
  | symbolStatusMessage (message : SymbolStatusMessage) -- 121
  | limitOrderAcceptedMessage (message : LimitOrderAcceptedMessage) -- 73
  | limitOrderRejectedMessage (message : LimitOrderRejectedMessage) -- 85
  | marketOrderAcceptedMessage (message : MarketOrderAcceptedMessage) -- 68
  | marketOrderRejectedMessage (message : MarketOrderRejectedMessage) -- 84
  | orderCanceledMessage (message : OrderCanceledMessage) -- 88
  | cancelRejectedMessage (message : CancelRejectedMessage) -- 87
  | orderModifiedMessage (message : OrderModifiedMessage) -- 89
  | modifyRejectedMessage (message : ModifyRejectedMessage) -- 78
  | orderReplacedMessage (message : OrderReplacedMessage) -- 74
  | replaceRejectedMessage (message : ReplaceRejectedMessage) -- 75
  | orderExecutedMessage (message : OrderExecutedMessage) -- 69
  | orderRestatedMessage (message : OrderRestatedMessage) -- 70
  | selfMatchPreventedMessage (message : SelfMatchPreventedMessage) -- 90
  | massCancelAcceptedMessage (message : MassCancelAcceptedMessage) -- 79
  | massCancelRejectedMessage (message : MassCancelRejectedMessage) -- 80
  | massCancelResultMessage (message : MassCancelResultMessage) -- 81
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .tradingSessionStatusMessage _ => 105
  | .defineSymbolMessage _ => 115
  | .symbolStatusMessage _ => 121
  | .limitOrderAcceptedMessage _ => 73
  | .limitOrderRejectedMessage _ => 85
  | .marketOrderAcceptedMessage _ => 68
  | .marketOrderRejectedMessage _ => 84
  | .orderCanceledMessage _ => 88
  | .cancelRejectedMessage _ => 87
  | .orderModifiedMessage _ => 89
  | .modifyRejectedMessage _ => 78
  | .orderReplacedMessage _ => 74
  | .replaceRejectedMessage _ => 75
  | .orderExecutedMessage _ => 69
  | .orderRestatedMessage _ => 70
  | .selfMatchPreventedMessage _ => 90
  | .massCancelAcceptedMessage _ => 79
  | .massCancelRejectedMessage _ => 80
  | .massCancelResultMessage _ => 81

def encode : SequencedMessage → List UInt8
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .defineSymbolMessage message => DefineSymbolMessage.encode message
  | .symbolStatusMessage message => SymbolStatusMessage.encode message
  | .limitOrderAcceptedMessage message => LimitOrderAcceptedMessage.encode message
  | .limitOrderRejectedMessage message => LimitOrderRejectedMessage.encode message
  | .marketOrderAcceptedMessage message => MarketOrderAcceptedMessage.encode message
  | .marketOrderRejectedMessage message => MarketOrderRejectedMessage.encode message
  | .orderCanceledMessage message => OrderCanceledMessage.encode message
  | .cancelRejectedMessage message => CancelRejectedMessage.encode message
  | .orderModifiedMessage message => OrderModifiedMessage.encode message
  | .modifyRejectedMessage message => ModifyRejectedMessage.encode message
  | .orderReplacedMessage message => OrderReplacedMessage.encode message
  | .replaceRejectedMessage message => ReplaceRejectedMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderRestatedMessage message => OrderRestatedMessage.encode message
  | .selfMatchPreventedMessage message => SelfMatchPreventedMessage.encode message
  | .massCancelAcceptedMessage message => MassCancelAcceptedMessage.encode message
  | .massCancelRejectedMessage message => MassCancelRejectedMessage.encode message
  | .massCancelResultMessage message => MassCancelResultMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 105 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 115 then (DefineSymbolMessage.decode bytes).map fun (message, rest) => (.defineSymbolMessage message, rest)
  else if tag = 121 then (SymbolStatusMessage.decode bytes).map fun (message, rest) => (.symbolStatusMessage message, rest)
  else if tag = 73 then (LimitOrderAcceptedMessage.decode bytes).map fun (message, rest) => (.limitOrderAcceptedMessage message, rest)
  else if tag = 85 then (LimitOrderRejectedMessage.decode bytes).map fun (message, rest) => (.limitOrderRejectedMessage message, rest)
  else if tag = 68 then (MarketOrderAcceptedMessage.decode bytes).map fun (message, rest) => (.marketOrderAcceptedMessage message, rest)
  else if tag = 84 then (MarketOrderRejectedMessage.decode bytes).map fun (message, rest) => (.marketOrderRejectedMessage message, rest)
  else if tag = 88 then (OrderCanceledMessage.decode bytes).map fun (message, rest) => (.orderCanceledMessage message, rest)
  else if tag = 87 then (CancelRejectedMessage.decode bytes).map fun (message, rest) => (.cancelRejectedMessage message, rest)
  else if tag = 89 then (OrderModifiedMessage.decode bytes).map fun (message, rest) => (.orderModifiedMessage message, rest)
  else if tag = 78 then (ModifyRejectedMessage.decode bytes).map fun (message, rest) => (.modifyRejectedMessage message, rest)
  else if tag = 74 then (OrderReplacedMessage.decode bytes).map fun (message, rest) => (.orderReplacedMessage message, rest)
  else if tag = 75 then (ReplaceRejectedMessage.decode bytes).map fun (message, rest) => (.replaceRejectedMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 70 then (OrderRestatedMessage.decode bytes).map fun (message, rest) => (.orderRestatedMessage message, rest)
  else if tag = 90 then (SelfMatchPreventedMessage.decode bytes).map fun (message, rest) => (.selfMatchPreventedMessage message, rest)
  else if tag = 79 then (MassCancelAcceptedMessage.decode bytes).map fun (message, rest) => (.massCancelAcceptedMessage message, rest)
  else if tag = 80 then (MassCancelRejectedMessage.decode bytes).map fun (message, rest) => (.massCancelRejectedMessage message, rest)
  else if tag = 81 then (MassCancelResultMessage.decode bytes).map fun (message, rest) => (.massCancelResultMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Tcp Sequenced Message -/
structure TcpSequencedMessage where
  streamId : BitVec 8
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace TcpSequencedMessage

def encode (message : TcpSequencedMessage) : List UInt8 :=
  encodeUInt 1 message.streamId
    ++ (encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage))

def decode (bytes : List UInt8) : Option (TcpSequencedMessage × List UInt8) := do
  let (streamId, bytes) ← decodeUInt 1 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode messageType bytes
  pure ({ streamId, sequencedMessage }, bytes)

theorem encode_length_pos (message : TcpSequencedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : TcpSequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TcpSequencedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TcpSequencedMessage

/-- Any Payload, selected by Packet Type -/
inductive Payload where
  | logonRequestPacket (message : LogonRequestPacket) -- 53
  | tcpUnsequencedMessage (message : TcpUnsequencedMessage) -- 54
  | debugMessage (message : DebugMessage) -- 48
  | endOfSessionMessage (message : EndOfSessionMessage) -- 52
  | logonResponseMessage (message : LogonResponseMessage) -- 49
  | tcpSequencedMessage (message : TcpSequencedMessage) -- 50
  deriving DecidableEq, Repr

namespace Payload

/-- The Packet Type each message is sent under -/
def tag : Payload → BitVec 8
  | .logonRequestPacket _ => 53
  | .tcpUnsequencedMessage _ => 54
  | .debugMessage _ => 48
  | .endOfSessionMessage _ => 52
  | .logonResponseMessage _ => 49
  | .tcpSequencedMessage _ => 50

def encode : Payload → List UInt8
  | .logonRequestPacket message => LogonRequestPacket.encode message
  | .tcpUnsequencedMessage message => TcpUnsequencedMessage.encode message
  | .debugMessage message => DebugMessage.encode message
  | .endOfSessionMessage message => EndOfSessionMessage.encode message
  | .logonResponseMessage message => LogonResponseMessage.encode message
  | .tcpSequencedMessage message => TcpSequencedMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option Payload :=
  if tag = 53 then (LogonRequestPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logonRequestPacket message) else none
  else if tag = 54 then (TcpUnsequencedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tcpUnsequencedMessage message) else none
  else if tag = 48 then (DebugMessage.decode bytes).map fun message => .debugMessage message
  else if tag = 52 then (EndOfSessionMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSessionMessage message) else none
  else if tag = 49 then (LogonResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logonResponseMessage message) else none
  else if tag = 50 then (TcpSequencedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tcpSequencedMessage message) else none
  else none

theorem decode_encode (message : Payload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | logonRequestPacket message => simp [decode, encode, tag, LogonRequestPacket.decode_encode_nil]
  | tcpUnsequencedMessage message => simp [decode, encode, tag, TcpUnsequencedMessage.decode_encode_nil]
  | debugMessage message => simp [decode, encode, tag, DebugMessage.decode_encode]
  | endOfSessionMessage message => simp [decode, encode, tag, EndOfSessionMessage.decode_encode_nil]
  | logonResponseMessage message => simp [decode, encode, tag, LogonResponseMessage.decode_encode_nil]
  | tcpSequencedMessage message => simp [decode, encode, tag, TcpSequencedMessage.decode_encode_nil]

end Payload

/-- Rake Tcp Message: the body, which the record carries with the proof it fits its frame -/
structure RakeTcpMessageBody where
  payload : Payload
  deriving DecidableEq, Repr

namespace RakeTcpMessageBody

def encodeBody (message : RakeTcpMessageBody) : List UInt8 :=
  encodeUIntLE 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option RakeTcpMessageBody := do
  let (packetType, bytes) ← decodeUIntLE 1 bytes
  let payload ← Payload.decode packetType bytes
  pure { payload }

theorem decodeBody_encodeBody (message : RakeTcpMessageBody) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end RakeTcpMessageBody

/-- Rake Tcp Message: the body with the proof its encoding fits Message Length, whose 2 bytes no bound of the fields fits -/
abbrev RakeTcpMessage := Fitting RakeTcpMessageBody.encodeBody 0 65536

namespace RakeTcpMessage

def encode (message : RakeTcpMessage) : List UInt8 :=
  encodeFramedLE 2 0 RakeTcpMessageBody.encodeBody message.val

def decode : List UInt8 → Option (RakeTcpMessage × List UInt8) :=
  decodeFittingAllLE 2 0 RakeTcpMessageBody.encodeBody RakeTcpMessageBody.decodeBody

@[simp] theorem decode_encode (message : RakeTcpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAllLE_encodeFramedLE 2 0 RakeTcpMessageBody.encodeBody RakeTcpMessageBody.decodeBody message (RakeTcpMessageBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : RakeTcpMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : RakeTcpMessage) : (encode message).length ≤ 65537 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramedLE_length]
  omega

end RakeTcpMessage

/-- Packet -/
structure Packet where
  rakeTcpMessage : List RakeTcpMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany RakeTcpMessage.encode message.rakeTcpMessage

def decode (bytes : List UInt8) : Option Packet := do
  let rakeTcpMessage ← decodeAll RakeTcpMessage.decode bytes.length bytes
  pure { rakeTcpMessage }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany RakeTcpMessage.encode RakeTcpMessage.decode RakeTcpMessage.decode_encode RakeTcpMessage.encode_length_pos message.rakeTcpMessage _ (encodeMany_length_ge RakeTcpMessage.encode RakeTcpMessage.encode_length_pos message.rakeTcpMessage), some_bind]
  rfl

end Packet

end Omi.TxseTxseequitiesSeedRakeV10
