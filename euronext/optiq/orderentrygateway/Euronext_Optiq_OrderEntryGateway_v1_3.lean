import Omi.Wire

/-!
# Euronext Order Entry Gateway v1.3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Execution Instruction is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Dark Execution Instruction is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Mifid Indicators is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Trading Session is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Open Close is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Ack Qualifiers is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Trade Qualifier is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Waiver Indicator is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EuronextOptiqOrderentrygatewaySbeV13

/-- New Order Message Free Text Section Group: 18 bytes -/
structure NewOrderMessageFreeTextSectionGroup where
  freeText : Alpha 18
  deriving DecidableEq, Repr

namespace NewOrderMessageFreeTextSectionGroup

def encode (message : NewOrderMessageFreeTextSectionGroup) : List UInt8 :=
  Alpha.encode message.freeText

def decode (bytes : List UInt8) : Option (NewOrderMessageFreeTextSectionGroup × List UInt8) := do
  let (freeText, bytes) ← Alpha.decode 18 bytes
  pure ({ freeText }, bytes)

@[simp] theorem encode_length (message : NewOrderMessageFreeTextSectionGroup) : (encode message).length = 18 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : NewOrderMessageFreeTextSectionGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderMessageFreeTextSectionGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderMessageFreeTextSectionGroup

/-- Free Text Groups -/
structure FreeTextGroups where
  blockLengthShort : BitVec 8
  newOrderMessageFreeTextSectionGroup : Bounded 1 NewOrderMessageFreeTextSectionGroup
  deriving DecidableEq, Repr

namespace FreeTextGroups

def encode (message : FreeTextGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.newOrderMessageFreeTextSectionGroup.val.length)
    ++ (encodeMany NewOrderMessageFreeTextSectionGroup.encode message.newOrderMessageFreeTextSectionGroup.val))

def decode (bytes : List UInt8) : Option (FreeTextGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (newOrderMessageFreeTextSectionGroup_, bytes) ← decodeMany NewOrderMessageFreeTextSectionGroup.decode numInGroup.toNat bytes
  if fits_newOrderMessageFreeTextSectionGroup : newOrderMessageFreeTextSectionGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, newOrderMessageFreeTextSectionGroup := ⟨newOrderMessageFreeTextSectionGroup_, fits_newOrderMessageFreeTextSectionGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : FreeTextGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FreeTextGroups) : (encode message).length ≤ 4592 := by
  have bound_newOrderMessageFreeTextSectionGroup := message.newOrderMessageFreeTextSectionGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const NewOrderMessageFreeTextSectionGroup.encode 18 NewOrderMessageFreeTextSectionGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : FreeTextGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 NewOrderMessageFreeTextSectionGroup.encode NewOrderMessageFreeTextSectionGroup.decode NewOrderMessageFreeTextSectionGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.newOrderMessageFreeTextSectionGroup.length_lt]
  rfl

end FreeTextGroups

/-- Mifid Short Codes Group: 12 bytes -/
structure MifidShortCodesGroup where
  investmentDecisionWFirmShortCode : BitVec 32
  nonExecutingBrokerShortCode : BitVec 32
  clientIdentificationShortcode : BitVec 32
  deriving DecidableEq, Repr

namespace MifidShortCodesGroup

def encode (message : MifidShortCodesGroup) : List UInt8 :=
  encodeUIntLE 4 message.investmentDecisionWFirmShortCode
    ++ (encodeUIntLE 4 message.nonExecutingBrokerShortCode
    ++ (encodeUIntLE 4 message.clientIdentificationShortcode))

def decode (bytes : List UInt8) : Option (MifidShortCodesGroup × List UInt8) := do
  let (investmentDecisionWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (nonExecutingBrokerShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortcode, bytes) ← decodeUIntLE 4 bytes
  pure ({ investmentDecisionWFirmShortCode, nonExecutingBrokerShortCode, clientIdentificationShortcode }, bytes)

@[simp] theorem encode_length (message : MifidShortCodesGroup) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MifidShortCodesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MifidShortCodesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MifidShortCodesGroup

/-- Mifid Short Codes Groups -/
structure MifidShortCodesGroups where
  blockLengthShort : BitVec 8
  mifidShortCodesGroup : Bounded 1 MifidShortCodesGroup
  deriving DecidableEq, Repr

namespace MifidShortCodesGroups

def encode (message : MifidShortCodesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.mifidShortCodesGroup.val.length)
    ++ (encodeMany MifidShortCodesGroup.encode message.mifidShortCodesGroup.val))

def decode (bytes : List UInt8) : Option (MifidShortCodesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (mifidShortCodesGroup_, bytes) ← decodeMany MifidShortCodesGroup.decode numInGroup.toNat bytes
  if fits_mifidShortCodesGroup : mifidShortCodesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, mifidShortCodesGroup := ⟨mifidShortCodesGroup_, fits_mifidShortCodesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MifidShortCodesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MifidShortCodesGroups) : (encode message).length ≤ 3062 := by
  have bound_mifidShortCodesGroup := message.mifidShortCodesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const MifidShortCodesGroup.encode 12 MifidShortCodesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MifidShortCodesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 MifidShortCodesGroup.encode MifidShortCodesGroup.decode MifidShortCodesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.mifidShortCodesGroup.length_lt]
  rfl

end MifidShortCodesGroups

/-- Order Optional Fields Group: 50 bytes -/
structure OrderOptionalFieldsGroup where
  stopPx : BitVec 64
  undisclosedPrice : BitVec 64
  disclosedQty : BitVec 64
  minOrderQty : BitVec 64
  quoteReqIdOptional : BitVec 64
  orderExpirationTime : BitVec 32
  orderExpirationDate : BitVec 16
  pegOffset : BitVec 8
  tradingSession : BitVec 8
  undisclosedIcebergType : BitVec 8
  stopTriggeredTimeInForce : BitVec 8
  deriving DecidableEq, Repr

namespace OrderOptionalFieldsGroup

def encode (message : OrderOptionalFieldsGroup) : List UInt8 :=
  encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.undisclosedPrice
    ++ (encodeUIntLE 8 message.disclosedQty
    ++ (encodeUIntLE 8 message.minOrderQty
    ++ (encodeUIntLE 8 message.quoteReqIdOptional
    ++ (encodeUIntLE 4 message.orderExpirationTime
    ++ (encodeUIntLE 2 message.orderExpirationDate
    ++ (encodeUInt 1 message.pegOffset
    ++ (encodeUIntLE 1 message.tradingSession
    ++ (encodeUInt 1 message.undisclosedIcebergType
    ++ (encodeUInt 1 message.stopTriggeredTimeInForce))))))))))

def decode (bytes : List UInt8) : Option (OrderOptionalFieldsGroup × List UInt8) := do
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (undisclosedPrice, bytes) ← decodeUIntLE 8 bytes
  let (disclosedQty, bytes) ← decodeUIntLE 8 bytes
  let (minOrderQty, bytes) ← decodeUIntLE 8 bytes
  let (quoteReqIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderExpirationTime, bytes) ← decodeUIntLE 4 bytes
  let (orderExpirationDate, bytes) ← decodeUIntLE 2 bytes
  let (pegOffset, bytes) ← decodeUInt 1 bytes
  let (tradingSession, bytes) ← decodeUIntLE 1 bytes
  let (undisclosedIcebergType, bytes) ← decodeUInt 1 bytes
  let (stopTriggeredTimeInForce, bytes) ← decodeUInt 1 bytes
  pure ({ stopPx, undisclosedPrice, disclosedQty, minOrderQty, quoteReqIdOptional, orderExpirationTime, orderExpirationDate, pegOffset, tradingSession, undisclosedIcebergType, stopTriggeredTimeInForce }, bytes)

@[simp] theorem encode_length (message : OrderOptionalFieldsGroup) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : OrderOptionalFieldsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderOptionalFieldsGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderOptionalFieldsGroup

/-- Order Optional Fields Groups -/
structure OrderOptionalFieldsGroups where
  blockLengthShort : BitVec 8
  orderOptionalFieldsGroup : Bounded 1 OrderOptionalFieldsGroup
  deriving DecidableEq, Repr

namespace OrderOptionalFieldsGroups

def encode (message : OrderOptionalFieldsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderOptionalFieldsGroup.val.length)
    ++ (encodeMany OrderOptionalFieldsGroup.encode message.orderOptionalFieldsGroup.val))

def decode (bytes : List UInt8) : Option (OrderOptionalFieldsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (orderOptionalFieldsGroup_, bytes) ← decodeMany OrderOptionalFieldsGroup.decode numInGroup.toNat bytes
  if fits_orderOptionalFieldsGroup : orderOptionalFieldsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, orderOptionalFieldsGroup := ⟨orderOptionalFieldsGroup_, fits_orderOptionalFieldsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderOptionalFieldsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderOptionalFieldsGroups) : (encode message).length ≤ 12752 := by
  have bound_orderOptionalFieldsGroup := message.orderOptionalFieldsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const OrderOptionalFieldsGroup.encode 50 OrderOptionalFieldsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderOptionalFieldsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OrderOptionalFieldsGroup.encode OrderOptionalFieldsGroup.decode OrderOptionalFieldsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderOptionalFieldsGroup.length_lt]
  rfl

end OrderOptionalFieldsGroups

/-- Order Clearing Fields Group: 34 bytes -/
structure OrderClearingFieldsGroup where
  clearingFirmId : Alpha 8
  clientId : Alpha 8
  accountNumber : Alpha 12
  technicalOrigin : BitVec 8
  openClose : BitVec 16
  clearingInstruction : BitVec 16
  accountTypeCross : BitVec 8
  deriving DecidableEq, Repr

namespace OrderClearingFieldsGroup

def encode (message : OrderClearingFieldsGroup) : List UInt8 :=
  Alpha.encode message.clearingFirmId
    ++ (Alpha.encode message.clientId
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 1 message.technicalOrigin
    ++ (encodeUIntLE 2 message.openClose
    ++ (encodeUIntLE 2 message.clearingInstruction
    ++ (encodeUInt 1 message.accountTypeCross))))))

def decode (bytes : List UInt8) : Option (OrderClearingFieldsGroup × List UInt8) := do
  let (clearingFirmId, bytes) ← Alpha.decode 8 bytes
  let (clientId, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 12 bytes
  let (technicalOrigin, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUIntLE 2 bytes
  let (clearingInstruction, bytes) ← decodeUIntLE 2 bytes
  let (accountTypeCross, bytes) ← decodeUInt 1 bytes
  pure ({ clearingFirmId, clientId, accountNumber, technicalOrigin, openClose, clearingInstruction, accountTypeCross }, bytes)

@[simp] theorem encode_length (message : OrderClearingFieldsGroup) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderClearingFieldsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderClearingFieldsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderClearingFieldsGroup

/-- Order Clearing Fields Groups -/
structure OrderClearingFieldsGroups where
  blockLengthShort : BitVec 8
  orderClearingFieldsGroup : Bounded 1 OrderClearingFieldsGroup
  deriving DecidableEq, Repr

namespace OrderClearingFieldsGroups

def encode (message : OrderClearingFieldsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderClearingFieldsGroup.val.length)
    ++ (encodeMany OrderClearingFieldsGroup.encode message.orderClearingFieldsGroup.val))

def decode (bytes : List UInt8) : Option (OrderClearingFieldsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (orderClearingFieldsGroup_, bytes) ← decodeMany OrderClearingFieldsGroup.decode numInGroup.toNat bytes
  if fits_orderClearingFieldsGroup : orderClearingFieldsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, orderClearingFieldsGroup := ⟨orderClearingFieldsGroup_, fits_orderClearingFieldsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderClearingFieldsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderClearingFieldsGroups) : (encode message).length ≤ 8672 := by
  have bound_orderClearingFieldsGroup := message.orderClearingFieldsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const OrderClearingFieldsGroup.encode 34 OrderClearingFieldsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderClearingFieldsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OrderClearingFieldsGroup.encode OrderClearingFieldsGroup.decode OrderClearingFieldsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderClearingFieldsGroup.length_lt]
  rfl

end OrderClearingFieldsGroups

/-- New Order Message -/
structure NewOrderMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  clientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  side : BitVec 8
  orderType : BitVec 8
  timeInForce : BitVec 8
  orderPx : BitVec 64
  orderQty : BitVec 64
  executionWithinFirmShortCode : BitVec 32
  tradingCapacity : BitVec 8
  accountType : BitVec 8
  lpRoleOptional : BitVec 8
  executionInstruction : BitVec 8
  darkExecutionInstruction : BitVec 8
  mifidIndicators : BitVec 8
  stpid : BitVec 16
  freeTextGroups : FreeTextGroups
  mifidShortCodesGroups : MifidShortCodesGroups
  orderOptionalFieldsGroups : OrderOptionalFieldsGroups
  orderClearingFieldsGroups : OrderClearingFieldsGroups
  deriving DecidableEq, Repr

namespace NewOrderMessage

def encode (message : NewOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.orderType
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUIntLE 8 message.orderPx
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCode
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.lpRoleOptional
    ++ (encodeUIntLE 1 message.executionInstruction
    ++ (encodeUIntLE 1 message.darkExecutionInstruction
    ++ (encodeUIntLE 1 message.mifidIndicators
    ++ (encodeUIntLE 2 message.stpid
    ++ (FreeTextGroups.encode message.freeTextGroups
    ++ (MifidShortCodesGroups.encode message.mifidShortCodesGroups
    ++ (OrderOptionalFieldsGroups.encode message.orderOptionalFieldsGroups
    ++ (OrderClearingFieldsGroups.encode message.orderClearingFieldsGroups))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (orderType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (orderPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (executionWithinFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (lpRoleOptional, bytes) ← decodeUInt 1 bytes
  let (executionInstruction, bytes) ← decodeUIntLE 1 bytes
  let (darkExecutionInstruction, bytes) ← decodeUIntLE 1 bytes
  let (mifidIndicators, bytes) ← decodeUIntLE 1 bytes
  let (stpid, bytes) ← decodeUIntLE 2 bytes
  let (freeTextGroups, bytes) ← FreeTextGroups.decode bytes
  let (mifidShortCodesGroups, bytes) ← MifidShortCodesGroups.decode bytes
  let (orderOptionalFieldsGroups, bytes) ← OrderOptionalFieldsGroups.decode bytes
  let (orderClearingFieldsGroups, bytes) ← OrderClearingFieldsGroups.decode bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, clientOrderId, symbolIndex, emm, side, orderType, timeInForce, orderPx, orderQty, executionWithinFirmShortCode, tradingCapacity, accountType, lpRoleOptional, executionInstruction, darkExecutionInstruction, mifidIndicators, stpid, freeTextGroups, mifidShortCodesGroups, orderOptionalFieldsGroups, orderClearingFieldsGroups }, bytes)

theorem encode_length_pos (message : NewOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderMessage) : (encode message).length ≤ 29142 := by
  have bound_freeTextGroups := FreeTextGroups.encode_length_le message.freeTextGroups
  have bound_mifidShortCodesGroups := MifidShortCodesGroups.encode_length_le message.mifidShortCodesGroups
  have bound_orderOptionalFieldsGroups := OrderOptionalFieldsGroups.encode_length_le message.orderOptionalFieldsGroups
  have bound_orderClearingFieldsGroups := OrderClearingFieldsGroups.encode_length_le message.orderClearingFieldsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : NewOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, FreeTextGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MifidShortCodesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderOptionalFieldsGroups.decode_encode, some_bind]
  dsimp only
  rw [OrderClearingFieldsGroups.decode_encode, some_bind]
  rfl

end NewOrderMessage

/-- Ack Message: 125 bytes -/
structure AckMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTimeOptional : BitVec 64
  oegInFromMember : BitVec 64
  oegOutTimeToMe : BitVec 64
  bookIn : BitVec 64
  bookOutTimeOptional : BitVec 64
  oegInFromMeOptional : BitVec 64
  oegOutToMemberOptional : BitVec 64
  clientOrderIdOptional : BitVec 64
  origClientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  sideOptional : BitVec 8
  ackType : BitVec 8
  ackPhase : BitVec 8
  orderIdOptional : BitVec 64
  orderPriority : BitVec 64
  orderPx : BitVec 64
  orderQtyOptional : BitVec 64
  ackQualifiers : BitVec 8
  deriving DecidableEq, Repr

namespace AckMessage

def encode (message : AckMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMember
    ++ (encodeUIntLE 8 message.oegOutTimeToMe
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMeOptional
    ++ (encodeUIntLE 8 message.oegOutToMemberOptional
    ++ (encodeUIntLE 8 message.clientOrderIdOptional
    ++ (encodeUIntLE 8 message.origClientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.sideOptional
    ++ (encodeUInt 1 message.ackType
    ++ (encodeUInt 1 message.ackPhase
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 8 message.orderPriority
    ++ (encodeUIntLE 8 message.orderPx
    ++ (encodeUIntLE 8 message.orderQtyOptional
    ++ (encodeUIntLE 1 message.ackQualifiers))))))))))))))))))))

def decode (bytes : List UInt8) : Option (AckMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMember, bytes) ← decodeUIntLE 8 bytes
  let (oegOutTimeToMe, bytes) ← decodeUIntLE 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegOutToMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (origClientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (sideOptional, bytes) ← decodeUInt 1 bytes
  let (ackType, bytes) ← decodeUInt 1 bytes
  let (ackPhase, bytes) ← decodeUInt 1 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderPriority, bytes) ← decodeUIntLE 8 bytes
  let (orderPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQtyOptional, bytes) ← decodeUIntLE 8 bytes
  let (ackQualifiers, bytes) ← decodeUIntLE 1 bytes
  pure ({ msgSeqNum, firmId, sendingTimeOptional, oegInFromMember, oegOutTimeToMe, bookIn, bookOutTimeOptional, oegInFromMeOptional, oegOutToMemberOptional, clientOrderIdOptional, origClientOrderId, symbolIndex, emm, sideOptional, ackType, ackPhase, orderIdOptional, orderPriority, orderPx, orderQtyOptional, ackQualifiers }, bytes)

@[simp] theorem encode_length (message : AckMessage) : (encode message).length = 125 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

end AckMessage

/-- Fill Optional Field Group: 32 bytes -/
structure FillOptionalFieldGroup where
  counterpartFirmId : Alpha 8
  otherLegLastPx : BitVec 64
  packageId : Alpha 12
  underlyingInstrumentId : BitVec 32
  deriving DecidableEq, Repr

namespace FillOptionalFieldGroup

def encode (message : FillOptionalFieldGroup) : List UInt8 :=
  Alpha.encode message.counterpartFirmId
    ++ (encodeUIntLE 8 message.otherLegLastPx
    ++ (Alpha.encode message.packageId
    ++ (encodeUIntLE 4 message.underlyingInstrumentId)))

def decode (bytes : List UInt8) : Option (FillOptionalFieldGroup × List UInt8) := do
  let (counterpartFirmId, bytes) ← Alpha.decode 8 bytes
  let (otherLegLastPx, bytes) ← decodeUIntLE 8 bytes
  let (packageId, bytes) ← Alpha.decode 12 bytes
  let (underlyingInstrumentId, bytes) ← decodeUIntLE 4 bytes
  pure ({ counterpartFirmId, otherLegLastPx, packageId, underlyingInstrumentId }, bytes)

@[simp] theorem encode_length (message : FillOptionalFieldGroup) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : FillOptionalFieldGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FillOptionalFieldGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end FillOptionalFieldGroup

/-- Fill Optional Field Groups -/
structure FillOptionalFieldGroups where
  blockLengthShort : BitVec 8
  fillOptionalFieldGroup : Bounded 1 FillOptionalFieldGroup
  deriving DecidableEq, Repr

namespace FillOptionalFieldGroups

def encode (message : FillOptionalFieldGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillOptionalFieldGroup.val.length)
    ++ (encodeMany FillOptionalFieldGroup.encode message.fillOptionalFieldGroup.val))

def decode (bytes : List UInt8) : Option (FillOptionalFieldGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (fillOptionalFieldGroup_, bytes) ← decodeMany FillOptionalFieldGroup.decode numInGroup.toNat bytes
  if fits_fillOptionalFieldGroup : fillOptionalFieldGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, fillOptionalFieldGroup := ⟨fillOptionalFieldGroup_, fits_fillOptionalFieldGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : FillOptionalFieldGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FillOptionalFieldGroups) : (encode message).length ≤ 8162 := by
  have bound_fillOptionalFieldGroup := message.fillOptionalFieldGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const FillOptionalFieldGroup.encode 32 FillOptionalFieldGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : FillOptionalFieldGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 FillOptionalFieldGroup.encode FillOptionalFieldGroup.decode FillOptionalFieldGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.fillOptionalFieldGroup.length_lt]
  rfl

end FillOptionalFieldGroups

/-- Fill Strategy Field Group: 21 bytes -/
structure FillStrategyFieldGroup where
  legLastPx : BitVec 64
  legLastQty : BitVec 64
  legInstrumentId : BitVec 32
  legSide : BitVec 8
  deriving DecidableEq, Repr

namespace FillStrategyFieldGroup

def encode (message : FillStrategyFieldGroup) : List UInt8 :=
  encodeUIntLE 8 message.legLastPx
    ++ (encodeUIntLE 8 message.legLastQty
    ++ (encodeUIntLE 4 message.legInstrumentId
    ++ (encodeUInt 1 message.legSide)))

def decode (bytes : List UInt8) : Option (FillStrategyFieldGroup × List UInt8) := do
  let (legLastPx, bytes) ← decodeUIntLE 8 bytes
  let (legLastQty, bytes) ← decodeUIntLE 8 bytes
  let (legInstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  pure ({ legLastPx, legLastQty, legInstrumentId, legSide }, bytes)

@[simp] theorem encode_length (message : FillStrategyFieldGroup) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : FillStrategyFieldGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FillStrategyFieldGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FillStrategyFieldGroup

/-- Fill Strategy Field Groups -/
structure FillStrategyFieldGroups where
  blockLengthShort : BitVec 8
  fillStrategyFieldGroup : Bounded 1 FillStrategyFieldGroup
  deriving DecidableEq, Repr

namespace FillStrategyFieldGroups

def encode (message : FillStrategyFieldGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillStrategyFieldGroup.val.length)
    ++ (encodeMany FillStrategyFieldGroup.encode message.fillStrategyFieldGroup.val))

def decode (bytes : List UInt8) : Option (FillStrategyFieldGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (fillStrategyFieldGroup_, bytes) ← decodeMany FillStrategyFieldGroup.decode numInGroup.toNat bytes
  if fits_fillStrategyFieldGroup : fillStrategyFieldGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, fillStrategyFieldGroup := ⟨fillStrategyFieldGroup_, fits_fillStrategyFieldGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : FillStrategyFieldGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FillStrategyFieldGroups) : (encode message).length ≤ 5357 := by
  have bound_fillStrategyFieldGroup := message.fillStrategyFieldGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const FillStrategyFieldGroup.encode 21 FillStrategyFieldGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : FillStrategyFieldGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 FillStrategyFieldGroup.encode FillStrategyFieldGroup.decode FillStrategyFieldGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.fillStrategyFieldGroup.length_lt]
  rfl

end FillStrategyFieldGroups

/-- Fill Message -/
structure FillMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  tradeTime : BitVec 64
  bookOutTimeOptional : BitVec 64
  oegInFromMeOptional : BitVec 64
  oegOutToMemberOptional : BitVec 64
  clientOrderIdOptional : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  side : BitVec 8
  tradeType : BitVec 8
  tradeQualifier : BitVec 8
  orderId : BitVec 64
  lastTradedPx : BitVec 64
  lastShares : BitVec 64
  leavesQty : BitVec 64
  executionId : BitVec 32
  executionPhase : BitVec 8
  fillOptionalFieldGroups : FillOptionalFieldGroups
  fillStrategyFieldGroups : FillStrategyFieldGroups
  deriving DecidableEq, Repr

namespace FillMessage

def encode (message : FillMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.tradeTime
    ++ (encodeUIntLE 8 message.bookOutTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMeOptional
    ++ (encodeUIntLE 8 message.oegOutToMemberOptional
    ++ (encodeUIntLE 8 message.clientOrderIdOptional
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.tradeType
    ++ (encodeUIntLE 1 message.tradeQualifier
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.lastTradedPx
    ++ (encodeUIntLE 8 message.lastShares
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 4 message.executionId
    ++ (encodeUInt 1 message.executionPhase
    ++ (FillOptionalFieldGroups.encode message.fillOptionalFieldGroups
    ++ (FillStrategyFieldGroups.encode message.fillStrategyFieldGroups)))))))))))))))))))

def decode (bytes : List UInt8) : Option (FillMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (tradeTime, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegOutToMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradeType, bytes) ← decodeUInt 1 bytes
  let (tradeQualifier, bytes) ← decodeUIntLE 1 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (lastTradedPx, bytes) ← decodeUIntLE 8 bytes
  let (lastShares, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (executionId, bytes) ← decodeUIntLE 4 bytes
  let (executionPhase, bytes) ← decodeUInt 1 bytes
  let (fillOptionalFieldGroups, bytes) ← FillOptionalFieldGroups.decode bytes
  let (fillStrategyFieldGroups, bytes) ← FillStrategyFieldGroups.decode bytes
  pure ({ msgSeqNum, firmId, tradeTime, bookOutTimeOptional, oegInFromMeOptional, oegOutToMemberOptional, clientOrderIdOptional, symbolIndex, emm, side, tradeType, tradeQualifier, orderId, lastTradedPx, lastShares, leavesQty, executionId, executionPhase, fillOptionalFieldGroups, fillStrategyFieldGroups }, bytes)

theorem encode_length_pos (message : FillMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FillMessage) : (encode message).length ≤ 13616 := by
  have bound_fillOptionalFieldGroups := FillOptionalFieldGroups.encode_length_le message.fillOptionalFieldGroups
  have bound_fillStrategyFieldGroups := FillStrategyFieldGroups.encode_length_le message.fillStrategyFieldGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : FillMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, FillOptionalFieldGroups.decode_encode, some_bind]
  dsimp only
  rw [FillStrategyFieldGroups.decode_encode, some_bind]
  rfl

end FillMessage

/-- Kill Message: 99 bytes -/
structure KillMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTimeOptional : BitVec 64
  oegInFromMember : BitVec 64
  oegOutTimeToMe : BitVec 64
  bookIn : BitVec 64
  bookOutTimeOptional : BitVec 64
  oegInFromMeOptional : BitVec 64
  oegOutToMemberOptional : BitVec 64
  clientOrderIdOptional : BitVec 64
  origClientOrderId : BitVec 64
  orderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  killReason : BitVec 16
  deriving DecidableEq, Repr

namespace KillMessage

def encode (message : KillMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMember
    ++ (encodeUIntLE 8 message.oegOutTimeToMe
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMeOptional
    ++ (encodeUIntLE 8 message.oegOutToMemberOptional
    ++ (encodeUIntLE 8 message.clientOrderIdOptional
    ++ (encodeUIntLE 8 message.origClientOrderId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 2 message.killReason))))))))))))))

def decode (bytes : List UInt8) : Option (KillMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMember, bytes) ← decodeUIntLE 8 bytes
  let (oegOutTimeToMe, bytes) ← decodeUIntLE 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegOutToMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (origClientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (killReason, bytes) ← decodeUIntLE 2 bytes
  pure ({ msgSeqNum, firmId, sendingTimeOptional, oegInFromMember, oegOutTimeToMe, bookIn, bookOutTimeOptional, oegInFromMeOptional, oegOutToMemberOptional, clientOrderIdOptional, origClientOrderId, orderId, symbolIndex, emm, killReason }, bytes)

@[simp] theorem encode_length (message : KillMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : KillMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : KillMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end KillMessage

/-- Cancel Replace Optional Field Group: 34 bytes -/
structure CancelReplaceOptionalFieldGroup where
  stopPx : BitVec 64
  pegOffset : BitVec 8
  undisclosedPrice : BitVec 64
  disclosedQty : BitVec 64
  orderExpirationTime : BitVec 32
  orderExpirationDate : BitVec 16
  tradingSession : BitVec 8
  stopTriggeredTimeInForce : BitVec 8
  undisclosedIcebergType : BitVec 8
  deriving DecidableEq, Repr

namespace CancelReplaceOptionalFieldGroup

def encode (message : CancelReplaceOptionalFieldGroup) : List UInt8 :=
  encodeUIntLE 8 message.stopPx
    ++ (encodeUInt 1 message.pegOffset
    ++ (encodeUIntLE 8 message.undisclosedPrice
    ++ (encodeUIntLE 8 message.disclosedQty
    ++ (encodeUIntLE 4 message.orderExpirationTime
    ++ (encodeUIntLE 2 message.orderExpirationDate
    ++ (encodeUIntLE 1 message.tradingSession
    ++ (encodeUInt 1 message.stopTriggeredTimeInForce
    ++ (encodeUInt 1 message.undisclosedIcebergType))))))))

def decode (bytes : List UInt8) : Option (CancelReplaceOptionalFieldGroup × List UInt8) := do
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (pegOffset, bytes) ← decodeUInt 1 bytes
  let (undisclosedPrice, bytes) ← decodeUIntLE 8 bytes
  let (disclosedQty, bytes) ← decodeUIntLE 8 bytes
  let (orderExpirationTime, bytes) ← decodeUIntLE 4 bytes
  let (orderExpirationDate, bytes) ← decodeUIntLE 2 bytes
  let (tradingSession, bytes) ← decodeUIntLE 1 bytes
  let (stopTriggeredTimeInForce, bytes) ← decodeUInt 1 bytes
  let (undisclosedIcebergType, bytes) ← decodeUInt 1 bytes
  pure ({ stopPx, pegOffset, undisclosedPrice, disclosedQty, orderExpirationTime, orderExpirationDate, tradingSession, stopTriggeredTimeInForce, undisclosedIcebergType }, bytes)

@[simp] theorem encode_length (message : CancelReplaceOptionalFieldGroup) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : CancelReplaceOptionalFieldGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelReplaceOptionalFieldGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CancelReplaceOptionalFieldGroup

/-- Cancel Replace Optional Field Groups -/
structure CancelReplaceOptionalFieldGroups where
  blockLengthShort : BitVec 8
  cancelReplaceOptionalFieldGroup : Bounded 1 CancelReplaceOptionalFieldGroup
  deriving DecidableEq, Repr

namespace CancelReplaceOptionalFieldGroups

def encode (message : CancelReplaceOptionalFieldGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.cancelReplaceOptionalFieldGroup.val.length)
    ++ (encodeMany CancelReplaceOptionalFieldGroup.encode message.cancelReplaceOptionalFieldGroup.val))

def decode (bytes : List UInt8) : Option (CancelReplaceOptionalFieldGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (cancelReplaceOptionalFieldGroup_, bytes) ← decodeMany CancelReplaceOptionalFieldGroup.decode numInGroup.toNat bytes
  if fits_cancelReplaceOptionalFieldGroup : cancelReplaceOptionalFieldGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, cancelReplaceOptionalFieldGroup := ⟨cancelReplaceOptionalFieldGroup_, fits_cancelReplaceOptionalFieldGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : CancelReplaceOptionalFieldGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : CancelReplaceOptionalFieldGroups) : (encode message).length ≤ 8672 := by
  have bound_cancelReplaceOptionalFieldGroup := message.cancelReplaceOptionalFieldGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const CancelReplaceOptionalFieldGroup.encode 34 CancelReplaceOptionalFieldGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : CancelReplaceOptionalFieldGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 CancelReplaceOptionalFieldGroup.encode CancelReplaceOptionalFieldGroup.decode CancelReplaceOptionalFieldGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.cancelReplaceOptionalFieldGroup.length_lt]
  rfl

end CancelReplaceOptionalFieldGroups

/-- Cancel Replace Clearing Fields Group: 33 bytes -/
structure CancelReplaceClearingFieldsGroup where
  clearingFirmId : Alpha 8
  clientId : Alpha 8
  accountNumber : Alpha 12
  technicalOrigin : BitVec 8
  openClose : BitVec 16
  clearingInstruction : BitVec 16
  deriving DecidableEq, Repr

namespace CancelReplaceClearingFieldsGroup

def encode (message : CancelReplaceClearingFieldsGroup) : List UInt8 :=
  Alpha.encode message.clearingFirmId
    ++ (Alpha.encode message.clientId
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 1 message.technicalOrigin
    ++ (encodeUIntLE 2 message.openClose
    ++ (encodeUIntLE 2 message.clearingInstruction)))))

def decode (bytes : List UInt8) : Option (CancelReplaceClearingFieldsGroup × List UInt8) := do
  let (clearingFirmId, bytes) ← Alpha.decode 8 bytes
  let (clientId, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 12 bytes
  let (technicalOrigin, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUIntLE 2 bytes
  let (clearingInstruction, bytes) ← decodeUIntLE 2 bytes
  pure ({ clearingFirmId, clientId, accountNumber, technicalOrigin, openClose, clearingInstruction }, bytes)

@[simp] theorem encode_length (message : CancelReplaceClearingFieldsGroup) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : CancelReplaceClearingFieldsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelReplaceClearingFieldsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CancelReplaceClearingFieldsGroup

/-- Cancel Replace Clearing Fields Groups -/
structure CancelReplaceClearingFieldsGroups where
  blockLengthShort : BitVec 8
  cancelReplaceClearingFieldsGroup : Bounded 1 CancelReplaceClearingFieldsGroup
  deriving DecidableEq, Repr

namespace CancelReplaceClearingFieldsGroups

def encode (message : CancelReplaceClearingFieldsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.cancelReplaceClearingFieldsGroup.val.length)
    ++ (encodeMany CancelReplaceClearingFieldsGroup.encode message.cancelReplaceClearingFieldsGroup.val))

def decode (bytes : List UInt8) : Option (CancelReplaceClearingFieldsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (cancelReplaceClearingFieldsGroup_, bytes) ← decodeMany CancelReplaceClearingFieldsGroup.decode numInGroup.toNat bytes
  if fits_cancelReplaceClearingFieldsGroup : cancelReplaceClearingFieldsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, cancelReplaceClearingFieldsGroup := ⟨cancelReplaceClearingFieldsGroup_, fits_cancelReplaceClearingFieldsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : CancelReplaceClearingFieldsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : CancelReplaceClearingFieldsGroups) : (encode message).length ≤ 8417 := by
  have bound_cancelReplaceClearingFieldsGroup := message.cancelReplaceClearingFieldsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const CancelReplaceClearingFieldsGroup.encode 33 CancelReplaceClearingFieldsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : CancelReplaceClearingFieldsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 CancelReplaceClearingFieldsGroup.encode CancelReplaceClearingFieldsGroup.decode CancelReplaceClearingFieldsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.cancelReplaceClearingFieldsGroup.length_lt]
  rfl

end CancelReplaceClearingFieldsGroups

/-- Cancel Replace Message -/
structure CancelReplaceMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  executionWithinFirmShortCode : BitVec 32
  clientIdentificationShortcode : BitVec 32
  clientOrderId : BitVec 64
  orderIdOptional : BitVec 64
  origClientOrderId : BitVec 64
  orderPx : BitVec 64
  orderQty : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  side : BitVec 8
  orderType : BitVec 8
  timeInForce : BitVec 8
  accountTypeOptional : BitVec 8
  lpRoleOptional : BitVec 8
  executionInstruction : BitVec 8
  darkExecutionInstruction : BitVec 8
  mifidIndicators : BitVec 8
  stpid : BitVec 16
  freeTextGroups : FreeTextGroups
  cancelReplaceOptionalFieldGroups : CancelReplaceOptionalFieldGroups
  cancelReplaceClearingFieldsGroups : CancelReplaceClearingFieldsGroups
  deriving DecidableEq, Repr

namespace CancelReplaceMessage

def encode (message : CancelReplaceMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCode
    ++ (encodeUIntLE 4 message.clientIdentificationShortcode
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 8 message.origClientOrderId
    ++ (encodeUIntLE 8 message.orderPx
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.orderType
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.accountTypeOptional
    ++ (encodeUInt 1 message.lpRoleOptional
    ++ (encodeUIntLE 1 message.executionInstruction
    ++ (encodeUIntLE 1 message.darkExecutionInstruction
    ++ (encodeUIntLE 1 message.mifidIndicators
    ++ (encodeUIntLE 2 message.stpid
    ++ (FreeTextGroups.encode message.freeTextGroups
    ++ (CancelReplaceOptionalFieldGroups.encode message.cancelReplaceOptionalFieldGroups
    ++ (CancelReplaceClearingFieldsGroups.encode message.cancelReplaceClearingFieldsGroups)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (CancelReplaceMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (executionWithinFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortcode, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (origClientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (orderPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (orderType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (accountTypeOptional, bytes) ← decodeUInt 1 bytes
  let (lpRoleOptional, bytes) ← decodeUInt 1 bytes
  let (executionInstruction, bytes) ← decodeUIntLE 1 bytes
  let (darkExecutionInstruction, bytes) ← decodeUIntLE 1 bytes
  let (mifidIndicators, bytes) ← decodeUIntLE 1 bytes
  let (stpid, bytes) ← decodeUIntLE 2 bytes
  let (freeTextGroups, bytes) ← FreeTextGroups.decode bytes
  let (cancelReplaceOptionalFieldGroups, bytes) ← CancelReplaceOptionalFieldGroups.decode bytes
  let (cancelReplaceClearingFieldsGroups, bytes) ← CancelReplaceClearingFieldsGroups.decode bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, executionWithinFirmShortCode, clientIdentificationShortcode, clientOrderId, orderIdOptional, origClientOrderId, orderPx, orderQty, symbolIndex, emm, side, orderType, timeInForce, accountTypeOptional, lpRoleOptional, executionInstruction, darkExecutionInstruction, mifidIndicators, stpid, freeTextGroups, cancelReplaceOptionalFieldGroups, cancelReplaceClearingFieldsGroups }, bytes)

theorem encode_length_pos (message : CancelReplaceMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : CancelReplaceMessage) : (encode message).length ≤ 21764 := by
  have bound_freeTextGroups := FreeTextGroups.encode_length_le message.freeTextGroups
  have bound_cancelReplaceOptionalFieldGroups := CancelReplaceOptionalFieldGroups.encode_length_le message.cancelReplaceOptionalFieldGroups
  have bound_cancelReplaceClearingFieldsGroups := CancelReplaceClearingFieldsGroups.encode_length_le message.cancelReplaceClearingFieldsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : CancelReplaceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, FreeTextGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CancelReplaceOptionalFieldGroups.decode_encode, some_bind]
  dsimp only
  rw [CancelReplaceClearingFieldsGroups.decode_encode, some_bind]
  rfl

end CancelReplaceMessage

/-- Collar Fields Group: 9 bytes -/
structure CollarFieldsGroup where
  collarRejType : BitVec 8
  breachedCollarPrice : BitVec 64
  deriving DecidableEq, Repr

namespace CollarFieldsGroup

def encode (message : CollarFieldsGroup) : List UInt8 :=
  encodeUInt 1 message.collarRejType
    ++ (encodeUIntLE 8 message.breachedCollarPrice)

def decode (bytes : List UInt8) : Option (CollarFieldsGroup × List UInt8) := do
  let (collarRejType, bytes) ← decodeUInt 1 bytes
  let (breachedCollarPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ collarRejType, breachedCollarPrice }, bytes)

@[simp] theorem encode_length (message : CollarFieldsGroup) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : CollarFieldsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CollarFieldsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CollarFieldsGroup

/-- Collar Fields Groups -/
structure CollarFieldsGroups where
  blockLengthShort : BitVec 8
  collarFieldsGroup : Bounded 1 CollarFieldsGroup
  deriving DecidableEq, Repr

namespace CollarFieldsGroups

def encode (message : CollarFieldsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.collarFieldsGroup.val.length)
    ++ (encodeMany CollarFieldsGroup.encode message.collarFieldsGroup.val))

def decode (bytes : List UInt8) : Option (CollarFieldsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (collarFieldsGroup_, bytes) ← decodeMany CollarFieldsGroup.decode numInGroup.toNat bytes
  if fits_collarFieldsGroup : collarFieldsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, collarFieldsGroup := ⟨collarFieldsGroup_, fits_collarFieldsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : CollarFieldsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : CollarFieldsGroups) : (encode message).length ≤ 2297 := by
  have bound_collarFieldsGroup := message.collarFieldsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const CollarFieldsGroup.encode 9 CollarFieldsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : CollarFieldsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 CollarFieldsGroup.encode CollarFieldsGroup.decode CollarFieldsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.collarFieldsGroup.length_lt]
  rfl

end CollarFieldsGroups

/-- Reject Message -/
structure RejectMessage where
  msgSeqNum : BitVec 32
  firmIdOptional : Alpha 8
  sendingTimeOptional : BitVec 64
  oegInFromMember : BitVec 64
  oegOutTimeToMe : BitVec 64
  bookInOptional : BitVec 64
  bookOutTimeOptional : BitVec 64
  oegInFromMeOptional : BitVec 64
  oegOutToMemberOptional : BitVec 64
  clientOrderIdOptional : BitVec 64
  orderIdOptional : BitVec 64
  symbolIndexOptional : BitVec 32
  emmOptional : BitVec 8
  rejectedMessage : BitVec 8
  errorCode : BitVec 16
  rejectedMessageId : BitVec 16
  collarFieldsGroups : CollarFieldsGroups
  deriving DecidableEq, Repr

namespace RejectMessage

def encode (message : RejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmIdOptional
    ++ (encodeUIntLE 8 message.sendingTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMember
    ++ (encodeUIntLE 8 message.oegOutTimeToMe
    ++ (encodeUIntLE 8 message.bookInOptional
    ++ (encodeUIntLE 8 message.bookOutTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMeOptional
    ++ (encodeUIntLE 8 message.oegOutToMemberOptional
    ++ (encodeUIntLE 8 message.clientOrderIdOptional
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 4 message.symbolIndexOptional
    ++ (encodeUInt 1 message.emmOptional
    ++ (encodeUInt 1 message.rejectedMessage
    ++ (encodeUIntLE 2 message.errorCode
    ++ (encodeUIntLE 2 message.rejectedMessageId
    ++ (CollarFieldsGroups.encode message.collarFieldsGroups))))))))))))))))

def decode (bytes : List UInt8) : Option (RejectMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmIdOptional, bytes) ← Alpha.decode 8 bytes
  let (sendingTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMember, bytes) ← decodeUIntLE 8 bytes
  let (oegOutTimeToMe, bytes) ← decodeUIntLE 8 bytes
  let (bookInOptional, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegOutToMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndexOptional, bytes) ← decodeUIntLE 4 bytes
  let (emmOptional, bytes) ← decodeUInt 1 bytes
  let (rejectedMessage, bytes) ← decodeUInt 1 bytes
  let (errorCode, bytes) ← decodeUIntLE 2 bytes
  let (rejectedMessageId, bytes) ← decodeUIntLE 2 bytes
  let (collarFieldsGroups, bytes) ← CollarFieldsGroups.decode bytes
  pure ({ msgSeqNum, firmIdOptional, sendingTimeOptional, oegInFromMember, oegOutTimeToMe, bookInOptional, bookOutTimeOptional, oegInFromMeOptional, oegOutToMemberOptional, clientOrderIdOptional, orderIdOptional, symbolIndexOptional, emmOptional, rejectedMessage, errorCode, rejectedMessageId, collarFieldsGroups }, bytes)

theorem encode_length_pos (message : RejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RejectMessage) : (encode message).length ≤ 2391 := by
  have bound_collarFieldsGroups := CollarFieldsGroups.encode_length_le message.collarFieldsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : RejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [CollarFieldsGroups.decode_encode, some_bind]
  rfl

end RejectMessage

/-- Clearing Dataset Group: 51 bytes -/
structure ClearingDatasetGroup where
  clearingFirmId : Alpha 8
  clientId : Alpha 8
  accountNumber : Alpha 12
  technicalOrigin : BitVec 8
  openClose : BitVec 16
  clearingInstruction : BitVec 16
  freeText : Alpha 18
  deriving DecidableEq, Repr

namespace ClearingDatasetGroup

def encode (message : ClearingDatasetGroup) : List UInt8 :=
  Alpha.encode message.clearingFirmId
    ++ (Alpha.encode message.clientId
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 1 message.technicalOrigin
    ++ (encodeUIntLE 2 message.openClose
    ++ (encodeUIntLE 2 message.clearingInstruction
    ++ (Alpha.encode message.freeText))))))

def decode (bytes : List UInt8) : Option (ClearingDatasetGroup × List UInt8) := do
  let (clearingFirmId, bytes) ← Alpha.decode 8 bytes
  let (clientId, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 12 bytes
  let (technicalOrigin, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUIntLE 2 bytes
  let (clearingInstruction, bytes) ← decodeUIntLE 2 bytes
  let (freeText, bytes) ← Alpha.decode 18 bytes
  pure ({ clearingFirmId, clientId, accountNumber, technicalOrigin, openClose, clearingInstruction, freeText }, bytes)

@[simp] theorem encode_length (message : ClearingDatasetGroup) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : ClearingDatasetGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingDatasetGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClearingDatasetGroup

/-- Clearing Dataset Groups -/
structure ClearingDatasetGroups where
  blockLengthShort : BitVec 8
  clearingDatasetGroup : Bounded 1 ClearingDatasetGroup
  deriving DecidableEq, Repr

namespace ClearingDatasetGroups

def encode (message : ClearingDatasetGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.clearingDatasetGroup.val.length)
    ++ (encodeMany ClearingDatasetGroup.encode message.clearingDatasetGroup.val))

def decode (bytes : List UInt8) : Option (ClearingDatasetGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (clearingDatasetGroup_, bytes) ← decodeMany ClearingDatasetGroup.decode numInGroup.toNat bytes
  if fits_clearingDatasetGroup : clearingDatasetGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, clearingDatasetGroup := ⟨clearingDatasetGroup_, fits_clearingDatasetGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ClearingDatasetGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClearingDatasetGroups) : (encode message).length ≤ 13007 := by
  have bound_clearingDatasetGroup := message.clearingDatasetGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const ClearingDatasetGroup.encode 51 ClearingDatasetGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : ClearingDatasetGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 ClearingDatasetGroup.encode ClearingDatasetGroup.decode ClearingDatasetGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.clearingDatasetGroup.length_lt]
  rfl

end ClearingDatasetGroups

/-- Quotes Rep Group: 37 bytes -/
structure QuotesRepGroup where
  bidSize : BitVec 64
  bidPx : BitVec 64
  offerSize : BitVec 64
  offerPx : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  deriving DecidableEq, Repr

namespace QuotesRepGroup

def encode (message : QuotesRepGroup) : List UInt8 :=
  encodeUIntLE 8 message.bidSize
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerSize
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm)))))

def decode (bytes : List UInt8) : Option (QuotesRepGroup × List UInt8) := do
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  pure ({ bidSize, bidPx, offerSize, offerPx, symbolIndex, emm }, bytes)

@[simp] theorem encode_length (message : QuotesRepGroup) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : QuotesRepGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuotesRepGroup) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuotesRepGroup

/-- Quotes Rep Groups -/
structure QuotesRepGroups where
  blockLengthShort : BitVec 8
  quotesRepGroup : Bounded 1 QuotesRepGroup
  deriving DecidableEq, Repr

namespace QuotesRepGroups

def encode (message : QuotesRepGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.quotesRepGroup.val.length)
    ++ (encodeMany QuotesRepGroup.encode message.quotesRepGroup.val))

def decode (bytes : List UInt8) : Option (QuotesRepGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (quotesRepGroup_, bytes) ← decodeMany QuotesRepGroup.decode numInGroup.toNat bytes
  if fits_quotesRepGroup : quotesRepGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, quotesRepGroup := ⟨quotesRepGroup_, fits_quotesRepGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuotesRepGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuotesRepGroups) : (encode message).length ≤ 9437 := by
  have bound_quotesRepGroup := message.quotesRepGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const QuotesRepGroup.encode 37 QuotesRepGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : QuotesRepGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 QuotesRepGroup.encode QuotesRepGroup.decode QuotesRepGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quotesRepGroup.length_lt]
  rfl

end QuotesRepGroups

/-- Quotes Message -/
structure QuotesMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  clientOrderId : BitVec 64
  executionWithinFirmShortCode : BitVec 32
  tradingCapacity : BitVec 8
  accountType : BitVec 8
  lpRole : BitVec 8
  mifidIndicators : BitVec 8
  rfeAnswer : BitVec 8
  mifidShortCodesGroups : MifidShortCodesGroups
  clearingDatasetGroups : ClearingDatasetGroups
  quotesRepGroups : QuotesRepGroups
  deriving DecidableEq, Repr

namespace QuotesMessage

def encode (message : QuotesMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCode
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.lpRole
    ++ (encodeUIntLE 1 message.mifidIndicators
    ++ (encodeUInt 1 message.rfeAnswer
    ++ (MifidShortCodesGroups.encode message.mifidShortCodesGroups
    ++ (ClearingDatasetGroups.encode message.clearingDatasetGroups
    ++ (QuotesRepGroups.encode message.quotesRepGroups))))))))))))

def decode (bytes : List UInt8) : Option (QuotesMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (executionWithinFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (lpRole, bytes) ← decodeUInt 1 bytes
  let (mifidIndicators, bytes) ← decodeUIntLE 1 bytes
  let (rfeAnswer, bytes) ← decodeUInt 1 bytes
  let (mifidShortCodesGroups, bytes) ← MifidShortCodesGroups.decode bytes
  let (clearingDatasetGroups, bytes) ← ClearingDatasetGroups.decode bytes
  let (quotesRepGroups, bytes) ← QuotesRepGroups.decode bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, clientOrderId, executionWithinFirmShortCode, tradingCapacity, accountType, lpRole, mifidIndicators, rfeAnswer, mifidShortCodesGroups, clearingDatasetGroups, quotesRepGroups }, bytes)

theorem encode_length_pos (message : QuotesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuotesMessage) : (encode message).length ≤ 25543 := by
  have bound_mifidShortCodesGroups := MifidShortCodesGroups.encode_length_le message.mifidShortCodesGroups
  have bound_clearingDatasetGroups := ClearingDatasetGroups.encode_length_le message.clearingDatasetGroups
  have bound_quotesRepGroups := QuotesRepGroups.encode_length_le message.quotesRepGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : QuotesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MifidShortCodesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingDatasetGroups.decode_encode, some_bind]
  dsimp only
  rw [QuotesRepGroups.decode_encode, some_bind]
  rfl

end QuotesMessage

/-- Quote Acks Group: 27 bytes -/
structure QuoteAcksGroup where
  bidOrderId : BitVec 64
  offerOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  buyRevisionFlag : BitVec 8
  sellRevisionFlag : BitVec 8
  bidErrorCode : BitVec 16
  offerErrorCode : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteAcksGroup

def encode (message : QuoteAcksGroup) : List UInt8 :=
  encodeUIntLE 8 message.bidOrderId
    ++ (encodeUIntLE 8 message.offerOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.buyRevisionFlag
    ++ (encodeUInt 1 message.sellRevisionFlag
    ++ (encodeUIntLE 2 message.bidErrorCode
    ++ (encodeUIntLE 2 message.offerErrorCode)))))))

def decode (bytes : List UInt8) : Option (QuoteAcksGroup × List UInt8) := do
  let (bidOrderId, bytes) ← decodeUIntLE 8 bytes
  let (offerOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (buyRevisionFlag, bytes) ← decodeUInt 1 bytes
  let (sellRevisionFlag, bytes) ← decodeUInt 1 bytes
  let (bidErrorCode, bytes) ← decodeUIntLE 2 bytes
  let (offerErrorCode, bytes) ← decodeUIntLE 2 bytes
  pure ({ bidOrderId, offerOrderId, symbolIndex, emm, buyRevisionFlag, sellRevisionFlag, bidErrorCode, offerErrorCode }, bytes)

@[simp] theorem encode_length (message : QuoteAcksGroup) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : QuoteAcksGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteAcksGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteAcksGroup

/-- Quote Acks Groups -/
structure QuoteAcksGroups where
  blockLengthShort : BitVec 8
  quoteAcksGroup : Bounded 1 QuoteAcksGroup
  deriving DecidableEq, Repr

namespace QuoteAcksGroups

def encode (message : QuoteAcksGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteAcksGroup.val.length)
    ++ (encodeMany QuoteAcksGroup.encode message.quoteAcksGroup.val))

def decode (bytes : List UInt8) : Option (QuoteAcksGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (quoteAcksGroup_, bytes) ← decodeMany QuoteAcksGroup.decode numInGroup.toNat bytes
  if fits_quoteAcksGroup : quoteAcksGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, quoteAcksGroup := ⟨quoteAcksGroup_, fits_quoteAcksGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteAcksGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteAcksGroups) : (encode message).length ≤ 6887 := by
  have bound_quoteAcksGroup := message.quoteAcksGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const QuoteAcksGroup.encode 27 QuoteAcksGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteAcksGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 QuoteAcksGroup.encode QuoteAcksGroup.decode QuoteAcksGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteAcksGroup.length_lt]
  rfl

end QuoteAcksGroups

/-- Quote Ack Message -/
structure QuoteAckMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTimeOptional : BitVec 64
  oegInFromMember : BitVec 64
  oegOutTimeToMe : BitVec 64
  bookIn : BitVec 64
  bookOutTimeOptional : BitVec 64
  oegInFromMeOptional : BitVec 64
  oegOutToMemberOptional : BitVec 64
  clientOrderId : BitVec 64
  accountType : BitVec 8
  lpRole : BitVec 8
  quoteAcksGroups : QuoteAcksGroups
  deriving DecidableEq, Repr

namespace QuoteAckMessage

def encode (message : QuoteAckMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMember
    ++ (encodeUIntLE 8 message.oegOutTimeToMe
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMeOptional
    ++ (encodeUIntLE 8 message.oegOutToMemberOptional
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.lpRole
    ++ (QuoteAcksGroups.encode message.quoteAcksGroups))))))))))))

def decode (bytes : List UInt8) : Option (QuoteAckMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMember, bytes) ← decodeUIntLE 8 bytes
  let (oegOutTimeToMe, bytes) ← decodeUIntLE 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegOutToMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (lpRole, bytes) ← decodeUInt 1 bytes
  let (quoteAcksGroups, bytes) ← QuoteAcksGroups.decode bytes
  pure ({ msgSeqNum, firmId, sendingTimeOptional, oegInFromMember, oegOutTimeToMe, bookIn, bookOutTimeOptional, oegInFromMeOptional, oegOutToMemberOptional, clientOrderId, accountType, lpRole, quoteAcksGroups }, bytes)

theorem encode_length_pos (message : QuoteAckMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteAckMessage) : (encode message).length ≤ 6965 := by
  have bound_quoteAcksGroups := QuoteAcksGroups.encode_length_le message.quoteAcksGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : QuoteAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [QuoteAcksGroups.decode_encode, some_bind]
  rfl

end QuoteAckMessage

/-- Quote Request Message: 62 bytes -/
structure QuoteRequestMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  executionWithinFirmShortCode : BitVec 32
  clientIdentificationShortcode : BitVec 32
  clientOrderId : BitVec 64
  orderQty : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  sideOptional : BitVec 8
  firmIdPublication : BitVec 8
  endClient : Alpha 11
  deriving DecidableEq, Repr

namespace QuoteRequestMessage

def encode (message : QuoteRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCode
    ++ (encodeUIntLE 4 message.clientIdentificationShortcode
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.sideOptional
    ++ (encodeUInt 1 message.firmIdPublication
    ++ (Alpha.encode message.endClient)))))))))))

def decode (bytes : List UInt8) : Option (QuoteRequestMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (executionWithinFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortcode, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (sideOptional, bytes) ← decodeUInt 1 bytes
  let (firmIdPublication, bytes) ← decodeUInt 1 bytes
  let (endClient, bytes) ← Alpha.decode 11 bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, executionWithinFirmShortCode, clientIdentificationShortcode, clientOrderId, orderQty, symbolIndex, emm, sideOptional, firmIdPublication, endClient }, bytes)

@[simp] theorem encode_length (message : QuoteRequestMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : QuoteRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteRequestMessage

/-- Cancel Request Message: 59 bytes -/
structure CancelRequestMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  executionWithinFirmShortCode : BitVec 32
  clientIdentificationShortcode : BitVec 32
  clientOrderId : BitVec 64
  orderIdOptional : BitVec 64
  origClientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  side : BitVec 8
  orderType : BitVec 8
  deriving DecidableEq, Repr

namespace CancelRequestMessage

def encode (message : CancelRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCode
    ++ (encodeUIntLE 4 message.clientIdentificationShortcode
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 8 message.origClientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.orderType)))))))))))

def decode (bytes : List UInt8) : Option (CancelRequestMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (executionWithinFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortcode, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (origClientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (orderType, bytes) ← decodeUInt 1 bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, executionWithinFirmShortCode, clientIdentificationShortcode, clientOrderId, orderIdOptional, origClientOrderId, symbolIndex, emm, side, orderType }, bytes)

@[simp] theorem encode_length (message : CancelRequestMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CancelRequestMessage

/-- Mass Cancel Message: 64 bytes -/
structure MassCancelMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  executionWithinFirmShortCode : BitVec 32
  clientIdentificationShortcode : BitVec 32
  clientOrderId : BitVec 64
  symbolIndexOptional : BitVec 32
  emmOptional : BitVec 8
  instrumentGroupCode : Alpha 2
  sideOptional : BitVec 8
  logicalAccessIdOptional : BitVec 32
  oePartitionIdOptional : BitVec 16
  contractId : BitVec 32
  maturity : Alpha 8
  accountTypeOptional : BitVec 8
  optionType : BitVec 8
  deriving DecidableEq, Repr

namespace MassCancelMessage

def encode (message : MassCancelMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCode
    ++ (encodeUIntLE 4 message.clientIdentificationShortcode
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolIndexOptional
    ++ (encodeUInt 1 message.emmOptional
    ++ (Alpha.encode message.instrumentGroupCode
    ++ (encodeUInt 1 message.sideOptional
    ++ (encodeUIntLE 4 message.logicalAccessIdOptional
    ++ (encodeUIntLE 2 message.oePartitionIdOptional
    ++ (encodeUIntLE 4 message.contractId
    ++ (Alpha.encode message.maturity
    ++ (encodeUInt 1 message.accountTypeOptional
    ++ (encodeUInt 1 message.optionType)))))))))))))))

def decode (bytes : List UInt8) : Option (MassCancelMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (executionWithinFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortcode, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndexOptional, bytes) ← decodeUIntLE 4 bytes
  let (emmOptional, bytes) ← decodeUInt 1 bytes
  let (instrumentGroupCode, bytes) ← Alpha.decode 2 bytes
  let (sideOptional, bytes) ← decodeUInt 1 bytes
  let (logicalAccessIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (oePartitionIdOptional, bytes) ← decodeUIntLE 2 bytes
  let (contractId, bytes) ← decodeUIntLE 4 bytes
  let (maturity, bytes) ← Alpha.decode 8 bytes
  let (accountTypeOptional, bytes) ← decodeUInt 1 bytes
  let (optionType, bytes) ← decodeUInt 1 bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, executionWithinFirmShortCode, clientIdentificationShortcode, clientOrderId, symbolIndexOptional, emmOptional, instrumentGroupCode, sideOptional, logicalAccessIdOptional, oePartitionIdOptional, contractId, maturity, accountTypeOptional, optionType }, bytes)

@[simp] theorem encode_length (message : MassCancelMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelMessage

/-- Mass Cancel Ack Message: 108 bytes -/
structure MassCancelAckMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTimeOptional : BitVec 64
  oegInFromMember : BitVec 64
  oegOutTimeToMe : BitVec 64
  bookIn : BitVec 64
  bookOutTime : BitVec 64
  oegInFromMe : BitVec 64
  oegOutToMember : BitVec 64
  clientOrderId : BitVec 64
  totalAffectedOrders : BitVec 32
  symbolIndexOptional : BitVec 32
  emmOptional : BitVec 8
  instrumentGroupCode : Alpha 2
  sideOptional : BitVec 8
  logicalAccessIdOptional : BitVec 32
  oePartitionIdOptional : BitVec 16
  contractId : BitVec 32
  maturity : Alpha 8
  accountTypeOptional : BitVec 8
  optionType : BitVec 8
  deriving DecidableEq, Repr

namespace MassCancelAckMessage

def encode (message : MassCancelAckMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMember
    ++ (encodeUIntLE 8 message.oegOutTimeToMe
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTime
    ++ (encodeUIntLE 8 message.oegInFromMe
    ++ (encodeUIntLE 8 message.oegOutToMember
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 4 message.totalAffectedOrders
    ++ (encodeUIntLE 4 message.symbolIndexOptional
    ++ (encodeUInt 1 message.emmOptional
    ++ (Alpha.encode message.instrumentGroupCode
    ++ (encodeUInt 1 message.sideOptional
    ++ (encodeUIntLE 4 message.logicalAccessIdOptional
    ++ (encodeUIntLE 2 message.oePartitionIdOptional
    ++ (encodeUIntLE 4 message.contractId
    ++ (Alpha.encode message.maturity
    ++ (encodeUInt 1 message.accountTypeOptional
    ++ (encodeUInt 1 message.optionType))))))))))))))))))))

def decode (bytes : List UInt8) : Option (MassCancelAckMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMember, bytes) ← decodeUIntLE 8 bytes
  let (oegOutTimeToMe, bytes) ← decodeUIntLE 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTime, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMe, bytes) ← decodeUIntLE 8 bytes
  let (oegOutToMember, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (totalAffectedOrders, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndexOptional, bytes) ← decodeUIntLE 4 bytes
  let (emmOptional, bytes) ← decodeUInt 1 bytes
  let (instrumentGroupCode, bytes) ← Alpha.decode 2 bytes
  let (sideOptional, bytes) ← decodeUInt 1 bytes
  let (logicalAccessIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (oePartitionIdOptional, bytes) ← decodeUIntLE 2 bytes
  let (contractId, bytes) ← decodeUIntLE 4 bytes
  let (maturity, bytes) ← Alpha.decode 8 bytes
  let (accountTypeOptional, bytes) ← decodeUInt 1 bytes
  let (optionType, bytes) ← decodeUInt 1 bytes
  pure ({ msgSeqNum, firmId, sendingTimeOptional, oegInFromMember, oegOutTimeToMe, bookIn, bookOutTime, oegInFromMe, oegOutToMember, clientOrderId, totalAffectedOrders, symbolIndexOptional, emmOptional, instrumentGroupCode, sideOptional, logicalAccessIdOptional, oePartitionIdOptional, contractId, maturity, accountTypeOptional, optionType }, bytes)

@[simp] theorem encode_length (message : MassCancelAckMessage) : (encode message).length = 108 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassCancelAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelAckMessage

/-- Open Order Request Message: 57 bytes -/
structure OpenOrderRequestMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  executionWithinFirmShortCode : BitVec 32
  clientIdentificationShortcode : BitVec 32
  clientOrderId : BitVec 64
  orderIdOptional : BitVec 64
  origClientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  deriving DecidableEq, Repr

namespace OpenOrderRequestMessage

def encode (message : OpenOrderRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCode
    ++ (encodeUIntLE 4 message.clientIdentificationShortcode
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 8 message.origClientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm)))))))))

def decode (bytes : List UInt8) : Option (OpenOrderRequestMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (executionWithinFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortcode, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (origClientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, executionWithinFirmShortCode, clientIdentificationShortcode, clientOrderId, orderIdOptional, origClientOrderId, symbolIndex, emm }, bytes)

@[simp] theorem encode_length (message : OpenOrderRequestMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OpenOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenOrderRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpenOrderRequestMessage

/-- Ownership Request Ack Message: 42 bytes -/
structure OwnershipRequestAckMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  clientOrderId : BitVec 64
  orderIdOptional : BitVec 64
  symbolIndex : BitVec 32
  logicalAccessIdOptional : BitVec 32
  oePartitionIdOptional : BitVec 16
  totalAffectedOrders : BitVec 32
  deriving DecidableEq, Repr

namespace OwnershipRequestAckMessage

def encode (message : OwnershipRequestAckMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.logicalAccessIdOptional
    ++ (encodeUIntLE 2 message.oePartitionIdOptional
    ++ (encodeUIntLE 4 message.totalAffectedOrders)))))))

def decode (bytes : List UInt8) : Option (OwnershipRequestAckMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (logicalAccessIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (oePartitionIdOptional, bytes) ← decodeUIntLE 2 bytes
  let (totalAffectedOrders, bytes) ← decodeUIntLE 4 bytes
  pure ({ msgSeqNum, firmId, clientOrderId, orderIdOptional, symbolIndex, logicalAccessIdOptional, oePartitionIdOptional, totalAffectedOrders }, bytes)

@[simp] theorem encode_length (message : OwnershipRequestAckMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OwnershipRequestAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OwnershipRequestAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

end OwnershipRequestAckMessage

/-- Ownership Request Message: 63 bytes -/
structure OwnershipRequestMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  executionWithinFirmShortCode : BitVec 32
  clientIdentificationShortcode : BitVec 32
  clientOrderId : BitVec 64
  orderIdOptional : BitVec 64
  origClientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  logicalAccessIdOptional : BitVec 32
  oePartitionIdOptional : BitVec 16
  deriving DecidableEq, Repr

namespace OwnershipRequestMessage

def encode (message : OwnershipRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCode
    ++ (encodeUIntLE 4 message.clientIdentificationShortcode
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 8 message.origClientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 4 message.logicalAccessIdOptional
    ++ (encodeUIntLE 2 message.oePartitionIdOptional)))))))))))

def decode (bytes : List UInt8) : Option (OwnershipRequestMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (executionWithinFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortcode, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (origClientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (logicalAccessIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (oePartitionIdOptional, bytes) ← decodeUIntLE 2 bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, executionWithinFirmShortCode, clientIdentificationShortcode, clientOrderId, orderIdOptional, origClientOrderId, symbolIndex, emm, logicalAccessIdOptional, oePartitionIdOptional }, bytes)

@[simp] theorem encode_length (message : OwnershipRequestMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OwnershipRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OwnershipRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OwnershipRequestMessage

/-- Trade Bust Notification Message: 69 bytes -/
structure TradeBustNotificationMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  bookIn : BitVec 64
  bookOutTimeOptional : BitVec 64
  oegInFromMeOptional : BitVec 64
  oegOutToMemberOptional : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  executionId : BitVec 32
  lastTradedPx : BitVec 64
  lastShares : BitVec 64
  deriving DecidableEq, Repr

namespace TradeBustNotificationMessage

def encode (message : TradeBustNotificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMeOptional
    ++ (encodeUIntLE 8 message.oegOutToMemberOptional
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 4 message.executionId
    ++ (encodeUIntLE 8 message.lastTradedPx
    ++ (encodeUIntLE 8 message.lastShares))))))))))

def decode (bytes : List UInt8) : Option (TradeBustNotificationMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegOutToMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (executionId, bytes) ← decodeUIntLE 4 bytes
  let (lastTradedPx, bytes) ← decodeUIntLE 8 bytes
  let (lastShares, bytes) ← decodeUIntLE 8 bytes
  pure ({ msgSeqNum, firmId, bookIn, bookOutTimeOptional, oegInFromMeOptional, oegOutToMemberOptional, symbolIndex, emm, executionId, lastTradedPx, lastShares }, bytes)

@[simp] theorem encode_length (message : TradeBustNotificationMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeBustNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeBustNotificationMessage

/-- Collar Breach Confirmation Message: 57 bytes -/
structure CollarBreachConfirmationMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  executionWithinFirmShortCode : BitVec 32
  clientIdentificationShortcode : BitVec 32
  clientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  orderIdOptional : BitVec 64
  origClientOrderId : BitVec 64
  deriving DecidableEq, Repr

namespace CollarBreachConfirmationMessage

def encode (message : CollarBreachConfirmationMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCode
    ++ (encodeUIntLE 4 message.clientIdentificationShortcode
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 8 message.origClientOrderId)))))))))

def decode (bytes : List UInt8) : Option (CollarBreachConfirmationMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (executionWithinFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortcode, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (origClientOrderId, bytes) ← decodeUIntLE 8 bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, executionWithinFirmShortCode, clientIdentificationShortcode, clientOrderId, symbolIndex, emm, orderIdOptional, origClientOrderId }, bytes)

@[simp] theorem encode_length (message : CollarBreachConfirmationMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CollarBreachConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CollarBreachConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CollarBreachConfirmationMessage

/-- Price Input Message: 50 bytes -/
structure PriceInputMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  executionWithinFirmShortCode : BitVec 32
  clientIdentificationShortcode : BitVec 32
  clientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  inputPriceType : BitVec 8
  priceOptional : BitVec 64
  deriving DecidableEq, Repr

namespace PriceInputMessage

def encode (message : PriceInputMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCode
    ++ (encodeUIntLE 4 message.clientIdentificationShortcode
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.inputPriceType
    ++ (encodeUIntLE 8 message.priceOptional)))))))))

def decode (bytes : List UInt8) : Option (PriceInputMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (executionWithinFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortcode, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (inputPriceType, bytes) ← decodeUInt 1 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, executionWithinFirmShortCode, clientIdentificationShortcode, clientOrderId, symbolIndex, emm, inputPriceType, priceOptional }, bytes)

@[simp] theorem encode_length (message : PriceInputMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PriceInputMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceInputMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end PriceInputMessage

/-- Liquidity Provider Command Message: 42 bytes -/
structure LiquidityProviderCommandMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  executionWithinFirmShortCode : BitVec 32
  clientIdentificationShortcode : BitVec 32
  clientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  lpActionCode : BitVec 8
  deriving DecidableEq, Repr

namespace LiquidityProviderCommandMessage

def encode (message : LiquidityProviderCommandMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCode
    ++ (encodeUIntLE 4 message.clientIdentificationShortcode
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.lpActionCode))))))))

def decode (bytes : List UInt8) : Option (LiquidityProviderCommandMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (executionWithinFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortcode, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (lpActionCode, bytes) ← decodeUInt 1 bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, executionWithinFirmShortCode, clientIdentificationShortcode, clientOrderId, symbolIndex, emm, lpActionCode }, bytes)

@[simp] theorem encode_length (message : LiquidityProviderCommandMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LiquidityProviderCommandMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LiquidityProviderCommandMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LiquidityProviderCommandMessage

/-- Ask For Quote Message: 18 bytes -/
structure AskForQuoteMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  symbolIndex : BitVec 32
  emm : BitVec 8
  afqReason : BitVec 8
  deriving DecidableEq, Repr

namespace AskForQuoteMessage

def encode (message : AskForQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.afqReason))))

def decode (bytes : List UInt8) : Option (AskForQuoteMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (afqReason, bytes) ← decodeUInt 1 bytes
  pure ({ msgSeqNum, firmId, symbolIndex, emm, afqReason }, bytes)

@[simp] theorem encode_length (message : AskForQuoteMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskForQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskForQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskForQuoteMessage

/-- Request For Execution Message: 17 bytes -/
structure RequestForExecutionMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  symbolIndex : BitVec 32
  emm : BitVec 8
  deriving DecidableEq, Repr

namespace RequestForExecutionMessage

def encode (message : RequestForExecutionMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm)))

def decode (bytes : List UInt8) : Option (RequestForExecutionMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  pure ({ msgSeqNum, firmId, symbolIndex, emm }, bytes)

@[simp] theorem encode_length (message : RequestForExecutionMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RequestForExecutionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestForExecutionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RequestForExecutionMessage

/-- Rfq Notification Message: 86 bytes -/
structure RfqNotificationMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  bookIn : BitVec 64
  bookOutTimeOptional : BitVec 64
  oegInFromMeOptional : BitVec 64
  oegOutToMemberOptional : BitVec 64
  quoteReqId : BitVec 64
  orderQty : BitVec 64
  counterpartFirmId : Alpha 8
  symbolIndex : BitVec 32
  emm : BitVec 8
  rfqUpdateType : BitVec 8
  sideOptional : BitVec 8
  endClient : Alpha 11
  deriving DecidableEq, Repr

namespace RfqNotificationMessage

def encode (message : RfqNotificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMeOptional
    ++ (encodeUIntLE 8 message.oegOutToMemberOptional
    ++ (encodeUIntLE 8 message.quoteReqId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (Alpha.encode message.counterpartFirmId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.rfqUpdateType
    ++ (encodeUInt 1 message.sideOptional
    ++ (Alpha.encode message.endClient)))))))))))))

def decode (bytes : List UInt8) : Option (RfqNotificationMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegOutToMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (quoteReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (counterpartFirmId, bytes) ← Alpha.decode 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (rfqUpdateType, bytes) ← decodeUInt 1 bytes
  let (sideOptional, bytes) ← decodeUInt 1 bytes
  let (endClient, bytes) ← Alpha.decode 11 bytes
  pure ({ msgSeqNum, firmId, bookIn, bookOutTimeOptional, oegInFromMeOptional, oegOutToMemberOptional, quoteReqId, orderQty, counterpartFirmId, symbolIndex, emm, rfqUpdateType, sideOptional, endClient }, bytes)

@[simp] theorem encode_length (message : RfqNotificationMessage) : (encode message).length = 86 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RfqNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RfqNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RfqNotificationMessage

/-- Rfq Matching Status Message: 76 bytes -/
structure RfqMatchingStatusMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  bookIn : BitVec 64
  bookOutTimeOptional : BitVec 64
  oegInFromMeOptional : BitVec 64
  oegOutToMemberOptional : BitVec 64
  quoteReqId : BitVec 64
  potentialMatchingPx : BitVec 64
  potentialMatchingQty : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  side : BitVec 8
  numberOfLps : BitVec 8
  recipientType : BitVec 8
  deriving DecidableEq, Repr

namespace RfqMatchingStatusMessage

def encode (message : RfqMatchingStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTimeOptional
    ++ (encodeUIntLE 8 message.oegInFromMeOptional
    ++ (encodeUIntLE 8 message.oegOutToMemberOptional
    ++ (encodeUIntLE 8 message.quoteReqId
    ++ (encodeUIntLE 8 message.potentialMatchingPx
    ++ (encodeUIntLE 8 message.potentialMatchingQty
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.numberOfLps
    ++ (encodeUInt 1 message.recipientType)))))))))))))

def decode (bytes : List UInt8) : Option (RfqMatchingStatusMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegInFromMeOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegOutToMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (quoteReqId, bytes) ← decodeUIntLE 8 bytes
  let (potentialMatchingPx, bytes) ← decodeUIntLE 8 bytes
  let (potentialMatchingQty, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (numberOfLps, bytes) ← decodeUInt 1 bytes
  let (recipientType, bytes) ← decodeUInt 1 bytes
  pure ({ msgSeqNum, firmId, bookIn, bookOutTimeOptional, oegInFromMeOptional, oegOutToMemberOptional, quoteReqId, potentialMatchingPx, potentialMatchingQty, symbolIndex, emm, side, numberOfLps, recipientType }, bytes)

@[simp] theorem encode_length (message : RfqMatchingStatusMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RfqMatchingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RfqMatchingStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RfqMatchingStatusMessage

/-- User Notification Message: 33 bytes -/
structure UserNotificationMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  executionWithinFirmShortCodeOptional : BitVec 32
  clientIdentificationShortcode : BitVec 32
  familyId : Alpha 8
  symbolIndexOptional : BitVec 32
  userStatus : BitVec 8
  deriving DecidableEq, Repr

namespace UserNotificationMessage

def encode (message : UserNotificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCodeOptional
    ++ (encodeUIntLE 4 message.clientIdentificationShortcode
    ++ (Alpha.encode message.familyId
    ++ (encodeUIntLE 4 message.symbolIndexOptional
    ++ (encodeUInt 1 message.userStatus))))))

def decode (bytes : List UInt8) : Option (UserNotificationMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (executionWithinFirmShortCodeOptional, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortcode, bytes) ← decodeUIntLE 4 bytes
  let (familyId, bytes) ← Alpha.decode 8 bytes
  let (symbolIndexOptional, bytes) ← decodeUIntLE 4 bytes
  let (userStatus, bytes) ← decodeUInt 1 bytes
  pure ({ msgSeqNum, firmId, executionWithinFirmShortCodeOptional, clientIdentificationShortcode, familyId, symbolIndexOptional, userStatus }, bytes)

@[simp] theorem encode_length (message : UserNotificationMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : UserNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end UserNotificationMessage

/-- Declaration Entry Message: 198 bytes -/
structure DeclarationEntryMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  clientOrderId : BitVec 64
  operationType : BitVec 8
  symbolIndex : BitVec 32
  emm : BitVec 8
  enteringCounterparty : Alpha 8
  side : BitVec 8
  quantity : BitVec 64
  priceOptional : BitVec 64
  executionWithinFirmShortCode : BitVec 32
  clientIdentificationShortcode : BitVec 32
  miCofSecondaryListing : Alpha 4
  centralisationDate : Alpha 10
  clearingFirmId : Alpha 8
  accountType : BitVec 8
  accountTypeCross : BitVec 8
  tradingCapacity : BitVec 8
  tradingCapacityCross : BitVec 8
  settlementPeriod : BitVec 8
  settlementFlag : BitVec 8
  guaranteeFlag : BitVec 8
  mifidIndicators : BitVec 8
  transactionPriceType : BitVec 8
  principalCode : Alpha 8
  principalCodeCross : Alpha 8
  startTimeVwap : BitVec 32
  endTimeVwap : BitVec 32
  grossTradeAmount : BitVec 64
  accountNumber : Alpha 12
  accountNumberCross : Alpha 12
  freeText : Alpha 18
  freeTextCross : Alpha 18
  investmentDecisionWFirmShortCode : BitVec 32
  clientIdentificationShortCodeCross : BitVec 32
  deriving DecidableEq, Repr

namespace DeclarationEntryMessage

def encode (message : DeclarationEntryMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUInt 1 message.operationType
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (Alpha.encode message.enteringCounterparty
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 4 message.executionWithinFirmShortCode
    ++ (encodeUIntLE 4 message.clientIdentificationShortcode
    ++ (Alpha.encode message.miCofSecondaryListing
    ++ (Alpha.encode message.centralisationDate
    ++ (Alpha.encode message.clearingFirmId
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.accountTypeCross
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.tradingCapacityCross
    ++ (encodeUInt 1 message.settlementPeriod
    ++ (encodeUInt 1 message.settlementFlag
    ++ (encodeUInt 1 message.guaranteeFlag
    ++ (encodeUIntLE 1 message.mifidIndicators
    ++ (encodeUInt 1 message.transactionPriceType
    ++ (Alpha.encode message.principalCode
    ++ (Alpha.encode message.principalCodeCross
    ++ (encodeUIntLE 4 message.startTimeVwap
    ++ (encodeUIntLE 4 message.endTimeVwap
    ++ (encodeUIntLE 8 message.grossTradeAmount
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.accountNumberCross
    ++ (Alpha.encode message.freeText
    ++ (Alpha.encode message.freeTextCross
    ++ (encodeUIntLE 4 message.investmentDecisionWFirmShortCode
    ++ (encodeUIntLE 4 message.clientIdentificationShortCodeCross)))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (DeclarationEntryMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (operationType, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (enteringCounterparty, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (executionWithinFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortcode, bytes) ← decodeUIntLE 4 bytes
  let (miCofSecondaryListing, bytes) ← Alpha.decode 4 bytes
  let (centralisationDate, bytes) ← Alpha.decode 10 bytes
  let (clearingFirmId, bytes) ← Alpha.decode 8 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (accountTypeCross, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (tradingCapacityCross, bytes) ← decodeUInt 1 bytes
  let (settlementPeriod, bytes) ← decodeUInt 1 bytes
  let (settlementFlag, bytes) ← decodeUInt 1 bytes
  let (guaranteeFlag, bytes) ← decodeUInt 1 bytes
  let (mifidIndicators, bytes) ← decodeUIntLE 1 bytes
  let (transactionPriceType, bytes) ← decodeUInt 1 bytes
  let (principalCode, bytes) ← Alpha.decode 8 bytes
  let (principalCodeCross, bytes) ← Alpha.decode 8 bytes
  let (startTimeVwap, bytes) ← decodeUIntLE 4 bytes
  let (endTimeVwap, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmount, bytes) ← decodeUIntLE 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 12 bytes
  let (accountNumberCross, bytes) ← Alpha.decode 12 bytes
  let (freeText, bytes) ← Alpha.decode 18 bytes
  let (freeTextCross, bytes) ← Alpha.decode 18 bytes
  let (investmentDecisionWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clientIdentificationShortCodeCross, bytes) ← decodeUIntLE 4 bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, clientOrderId, operationType, symbolIndex, emm, enteringCounterparty, side, quantity, priceOptional, executionWithinFirmShortCode, clientIdentificationShortcode, miCofSecondaryListing, centralisationDate, clearingFirmId, accountType, accountTypeCross, tradingCapacity, tradingCapacityCross, settlementPeriod, settlementFlag, guaranteeFlag, mifidIndicators, transactionPriceType, principalCode, principalCodeCross, startTimeVwap, endTimeVwap, grossTradeAmount, accountNumber, accountNumberCross, freeText, freeTextCross, investmentDecisionWFirmShortCode, clientIdentificationShortCodeCross }, bytes)

@[simp] theorem encode_length (message : DeclarationEntryMessage) : (encode message).length = 198 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DeclarationEntryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : DeclarationEntryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeclarationEntryMessage

/-- Declaration Entry Ack Message: 40 bytes -/
structure DeclarationEntryAckMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  declarationIdOptional : BitVec 64
  clientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  miCofSecondaryListing : Alpha 4
  operationType : BitVec 8
  preMatchingType : BitVec 8
  waiverIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace DeclarationEntryAckMessage

def encode (message : DeclarationEntryAckMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.declarationIdOptional
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (Alpha.encode message.miCofSecondaryListing
    ++ (encodeUInt 1 message.operationType
    ++ (encodeUInt 1 message.preMatchingType
    ++ (encodeUIntLE 1 message.waiverIndicator)))))))))

def decode (bytes : List UInt8) : Option (DeclarationEntryAckMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (declarationIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (miCofSecondaryListing, bytes) ← Alpha.decode 4 bytes
  let (operationType, bytes) ← decodeUInt 1 bytes
  let (preMatchingType, bytes) ← decodeUInt 1 bytes
  let (waiverIndicator, bytes) ← decodeUIntLE 1 bytes
  pure ({ msgSeqNum, firmId, declarationIdOptional, clientOrderId, symbolIndex, emm, miCofSecondaryListing, operationType, preMatchingType, waiverIndicator }, bytes)

@[simp] theorem encode_length (message : DeclarationEntryAckMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DeclarationEntryAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeclarationEntryAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeclarationEntryAckMessage

/-- Declaration Notice Message: 201 bytes -/
structure DeclarationNoticeMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  clientOrderIdOptional : BitVec 64
  declarationId : BitVec 64
  declarationStatus : BitVec 8
  operationType : BitVec 8
  symbolIndex : BitVec 32
  emm : BitVec 8
  enteringCounterparty : Alpha 8
  sideOptional : BitVec 8
  quantity : BitVec 64
  priceOptional : BitVec 64
  preMatchingType : BitVec 8
  tradeTimeOptional : BitVec 64
  miCofSecondaryListing : Alpha 4
  centralisationDate : Alpha 10
  clearingFirmId : Alpha 8
  accountTypeOptional : BitVec 8
  accountTypeCross : BitVec 8
  tradingCapacityOptional : BitVec 8
  tradingCapacityCross : BitVec 8
  settlementFlagOptional : BitVec 8
  settlementPeriodOptional : BitVec 8
  guaranteeFlagOptional : BitVec 8
  transactionPriceType : BitVec 8
  principalCode : Alpha 8
  principalCodeCross : Alpha 8
  startTimeVwap : BitVec 32
  endTimeVwap : BitVec 32
  grossTradeAmount : BitVec 64
  accountNumber : Alpha 12
  accountNumberCross : Alpha 12
  freeText : Alpha 18
  freeTextCross : Alpha 18
  waiverIndicator : BitVec 8
  previousDayIndicator : BitVec 8
  miscellaneousFeeAmount : BitVec 64
  deriving DecidableEq, Repr

namespace DeclarationNoticeMessage

def encode (message : DeclarationNoticeMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.clientOrderIdOptional
    ++ (encodeUIntLE 8 message.declarationId
    ++ (encodeUInt 1 message.declarationStatus
    ++ (encodeUInt 1 message.operationType
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (Alpha.encode message.enteringCounterparty
    ++ (encodeUInt 1 message.sideOptional
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUInt 1 message.preMatchingType
    ++ (encodeUIntLE 8 message.tradeTimeOptional
    ++ (Alpha.encode message.miCofSecondaryListing
    ++ (Alpha.encode message.centralisationDate
    ++ (Alpha.encode message.clearingFirmId
    ++ (encodeUInt 1 message.accountTypeOptional
    ++ (encodeUInt 1 message.accountTypeCross
    ++ (encodeUInt 1 message.tradingCapacityOptional
    ++ (encodeUInt 1 message.tradingCapacityCross
    ++ (encodeUInt 1 message.settlementFlagOptional
    ++ (encodeUInt 1 message.settlementPeriodOptional
    ++ (encodeUInt 1 message.guaranteeFlagOptional
    ++ (encodeUInt 1 message.transactionPriceType
    ++ (Alpha.encode message.principalCode
    ++ (Alpha.encode message.principalCodeCross
    ++ (encodeUIntLE 4 message.startTimeVwap
    ++ (encodeUIntLE 4 message.endTimeVwap
    ++ (encodeUIntLE 8 message.grossTradeAmount
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.accountNumberCross
    ++ (Alpha.encode message.freeText
    ++ (Alpha.encode message.freeTextCross
    ++ (encodeUIntLE 1 message.waiverIndicator
    ++ (encodeUInt 1 message.previousDayIndicator
    ++ (encodeUIntLE 8 message.miscellaneousFeeAmount))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (DeclarationNoticeMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (clientOrderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (declarationId, bytes) ← decodeUIntLE 8 bytes
  let (declarationStatus, bytes) ← decodeUInt 1 bytes
  let (operationType, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (enteringCounterparty, bytes) ← Alpha.decode 8 bytes
  let (sideOptional, bytes) ← decodeUInt 1 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (preMatchingType, bytes) ← decodeUInt 1 bytes
  let (tradeTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (miCofSecondaryListing, bytes) ← Alpha.decode 4 bytes
  let (centralisationDate, bytes) ← Alpha.decode 10 bytes
  let (clearingFirmId, bytes) ← Alpha.decode 8 bytes
  let (accountTypeOptional, bytes) ← decodeUInt 1 bytes
  let (accountTypeCross, bytes) ← decodeUInt 1 bytes
  let (tradingCapacityOptional, bytes) ← decodeUInt 1 bytes
  let (tradingCapacityCross, bytes) ← decodeUInt 1 bytes
  let (settlementFlagOptional, bytes) ← decodeUInt 1 bytes
  let (settlementPeriodOptional, bytes) ← decodeUInt 1 bytes
  let (guaranteeFlagOptional, bytes) ← decodeUInt 1 bytes
  let (transactionPriceType, bytes) ← decodeUInt 1 bytes
  let (principalCode, bytes) ← Alpha.decode 8 bytes
  let (principalCodeCross, bytes) ← Alpha.decode 8 bytes
  let (startTimeVwap, bytes) ← decodeUIntLE 4 bytes
  let (endTimeVwap, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmount, bytes) ← decodeUIntLE 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 12 bytes
  let (accountNumberCross, bytes) ← Alpha.decode 12 bytes
  let (freeText, bytes) ← Alpha.decode 18 bytes
  let (freeTextCross, bytes) ← Alpha.decode 18 bytes
  let (waiverIndicator, bytes) ← decodeUIntLE 1 bytes
  let (previousDayIndicator, bytes) ← decodeUInt 1 bytes
  let (miscellaneousFeeAmount, bytes) ← decodeUIntLE 8 bytes
  pure ({ msgSeqNum, firmId, clientOrderIdOptional, declarationId, declarationStatus, operationType, symbolIndex, emm, enteringCounterparty, sideOptional, quantity, priceOptional, preMatchingType, tradeTimeOptional, miCofSecondaryListing, centralisationDate, clearingFirmId, accountTypeOptional, accountTypeCross, tradingCapacityOptional, tradingCapacityCross, settlementFlagOptional, settlementPeriodOptional, guaranteeFlagOptional, transactionPriceType, principalCode, principalCodeCross, startTimeVwap, endTimeVwap, grossTradeAmount, accountNumber, accountNumberCross, freeText, freeTextCross, waiverIndicator, previousDayIndicator, miscellaneousFeeAmount }, bytes)

@[simp] theorem encode_length (message : DeclarationNoticeMessage) : (encode message).length = 201 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DeclarationNoticeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : DeclarationNoticeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeclarationNoticeMessage

/-- Declaration Cancel And Refusal Message: 42 bytes -/
structure DeclarationCancelAndRefusalMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  clientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  declarationId : BitVec 64
  actionType : BitVec 8
  deriving DecidableEq, Repr

namespace DeclarationCancelAndRefusalMessage

def encode (message : DeclarationCancelAndRefusalMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.declarationId
    ++ (encodeUInt 1 message.actionType)))))))

def decode (bytes : List UInt8) : Option (DeclarationCancelAndRefusalMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (declarationId, bytes) ← decodeUIntLE 8 bytes
  let (actionType, bytes) ← decodeUInt 1 bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, clientOrderId, symbolIndex, emm, declarationId, actionType }, bytes)

@[simp] theorem encode_length (message : DeclarationCancelAndRefusalMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DeclarationCancelAndRefusalMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeclarationCancelAndRefusalMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DeclarationCancelAndRefusalMessage

/-- Fund Price Input Message: 42 bytes -/
structure FundPriceInputMessage where
  clMsgSeqNum : BitVec 32
  firmId : Alpha 8
  sendingTime : BitVec 64
  clientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  price : BitVec 64
  bypassIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace FundPriceInputMessage

def encode (message : FundPriceInputMessage) : List UInt8 :=
  encodeUIntLE 4 message.clMsgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUInt 1 message.bypassIndicator)))))))

def decode (bytes : List UInt8) : Option (FundPriceInputMessage × List UInt8) := do
  let (clMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (bypassIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ clMsgSeqNum, firmId, sendingTime, clientOrderId, symbolIndex, emm, price, bypassIndicator }, bytes)

@[simp] theorem encode_length (message : FundPriceInputMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FundPriceInputMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FundPriceInputMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FundPriceInputMessage

/-- Fund Price Input Ack Message: 34 bytes -/
structure FundPriceInputAckMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  clientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  price : BitVec 64
  bypassIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace FundPriceInputAckMessage

def encode (message : FundPriceInputAckMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUInt 1 message.bypassIndicator))))))

def decode (bytes : List UInt8) : Option (FundPriceInputAckMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (bypassIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ msgSeqNum, firmId, clientOrderId, symbolIndex, emm, price, bypassIndicator }, bytes)

@[simp] theorem encode_length (message : FundPriceInputAckMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FundPriceInputAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FundPriceInputAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FundPriceInputAckMessage

/-- Declaration Entry Reject Message: 35 bytes -/
structure DeclarationEntryRejectMessage where
  msgSeqNum : BitVec 32
  firmId : Alpha 8
  clientOrderId : BitVec 64
  symbolIndex : BitVec 32
  emmOptional : BitVec 8
  miCofSecondaryListing : Alpha 4
  operationType : BitVec 8
  errorCode : BitVec 16
  rejectedMessage : BitVec 8
  rejectedMessageId : BitVec 16
  deriving DecidableEq, Repr

namespace DeclarationEntryRejectMessage

def encode (message : DeclarationEntryRejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emmOptional
    ++ (Alpha.encode message.miCofSecondaryListing
    ++ (encodeUInt 1 message.operationType
    ++ (encodeUIntLE 2 message.errorCode
    ++ (encodeUInt 1 message.rejectedMessage
    ++ (encodeUIntLE 2 message.rejectedMessageId)))))))))

def decode (bytes : List UInt8) : Option (DeclarationEntryRejectMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emmOptional, bytes) ← decodeUInt 1 bytes
  let (miCofSecondaryListing, bytes) ← Alpha.decode 4 bytes
  let (operationType, bytes) ← decodeUInt 1 bytes
  let (errorCode, bytes) ← decodeUIntLE 2 bytes
  let (rejectedMessage, bytes) ← decodeUInt 1 bytes
  let (rejectedMessageId, bytes) ← decodeUIntLE 2 bytes
  pure ({ msgSeqNum, firmId, clientOrderId, symbolIndex, emmOptional, miCofSecondaryListing, operationType, errorCode, rejectedMessage, rejectedMessageId }, bytes)

@[simp] theorem encode_length (message : DeclarationEntryRejectMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DeclarationEntryRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeclarationEntryRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeclarationEntryRejectMessage

/-- Instrument Synchronization Group: 5 bytes -/
structure InstrumentSynchronizationGroup where
  symbolIndex : BitVec 32
  emm : BitVec 8
  deriving DecidableEq, Repr

namespace InstrumentSynchronizationGroup

def encode (message : InstrumentSynchronizationGroup) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm)

def decode (bytes : List UInt8) : Option (InstrumentSynchronizationGroup × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  pure ({ symbolIndex, emm }, bytes)

@[simp] theorem encode_length (message : InstrumentSynchronizationGroup) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : InstrumentSynchronizationGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentSynchronizationGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InstrumentSynchronizationGroup

/-- Instrument Synchronization Groups -/
structure InstrumentSynchronizationGroups where
  blockLengthShort : BitVec 8
  instrumentSynchronizationGroup : Bounded 1 InstrumentSynchronizationGroup
  deriving DecidableEq, Repr

namespace InstrumentSynchronizationGroups

def encode (message : InstrumentSynchronizationGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentSynchronizationGroup.val.length)
    ++ (encodeMany InstrumentSynchronizationGroup.encode message.instrumentSynchronizationGroup.val))

def decode (bytes : List UInt8) : Option (InstrumentSynchronizationGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (instrumentSynchronizationGroup_, bytes) ← decodeMany InstrumentSynchronizationGroup.decode numInGroup.toNat bytes
  if fits_instrumentSynchronizationGroup : instrumentSynchronizationGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, instrumentSynchronizationGroup := ⟨instrumentSynchronizationGroup_, fits_instrumentSynchronizationGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : InstrumentSynchronizationGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InstrumentSynchronizationGroups) : (encode message).length ≤ 1277 := by
  have bound_instrumentSynchronizationGroup := message.instrumentSynchronizationGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const InstrumentSynchronizationGroup.encode 5 InstrumentSynchronizationGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : InstrumentSynchronizationGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 InstrumentSynchronizationGroup.encode InstrumentSynchronizationGroup.decode InstrumentSynchronizationGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instrumentSynchronizationGroup.length_lt]
  rfl

end InstrumentSynchronizationGroups

/-- Instrument Synchronization List Message -/
structure InstrumentSynchronizationListMessage where
  msgSeqNum : BitVec 32
  oegOutToMemberOptional : BitVec 64
  resynchronizationId : BitVec 16
  instrumentSynchronizationGroups : InstrumentSynchronizationGroups
  deriving DecidableEq, Repr

namespace InstrumentSynchronizationListMessage

def encode (message : InstrumentSynchronizationListMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.oegOutToMemberOptional
    ++ (encodeUIntLE 2 message.resynchronizationId
    ++ (InstrumentSynchronizationGroups.encode message.instrumentSynchronizationGroups)))

def decode (bytes : List UInt8) : Option (InstrumentSynchronizationListMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (oegOutToMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (resynchronizationId, bytes) ← decodeUIntLE 2 bytes
  let (instrumentSynchronizationGroups, bytes) ← InstrumentSynchronizationGroups.decode bytes
  pure ({ msgSeqNum, oegOutToMemberOptional, resynchronizationId, instrumentSynchronizationGroups }, bytes)

theorem encode_length_pos (message : InstrumentSynchronizationListMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InstrumentSynchronizationListMessage) : (encode message).length ≤ 1291 := by
  have bound_instrumentSynchronizationGroups := InstrumentSynchronizationGroups.encode_length_le message.instrumentSynchronizationGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : InstrumentSynchronizationListMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [InstrumentSynchronizationGroups.decode_encode, some_bind]
  rfl

end InstrumentSynchronizationListMessage

/-- Synchronization Time Message: 22 bytes -/
structure SynchronizationTimeMessage where
  msgSeqNum : BitVec 32
  oegOutToMemberOptional : BitVec 64
  resynchronizationId : BitVec 16
  lastBookInTime : BitVec 64
  deriving DecidableEq, Repr

namespace SynchronizationTimeMessage

def encode (message : SynchronizationTimeMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.oegOutToMemberOptional
    ++ (encodeUIntLE 2 message.resynchronizationId
    ++ (encodeUIntLE 8 message.lastBookInTime)))

def decode (bytes : List UInt8) : Option (SynchronizationTimeMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (oegOutToMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (resynchronizationId, bytes) ← decodeUIntLE 2 bytes
  let (lastBookInTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ msgSeqNum, oegOutToMemberOptional, resynchronizationId, lastBookInTime }, bytes)

@[simp] theorem encode_length (message : SynchronizationTimeMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SynchronizationTimeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SynchronizationTimeMessage) (rest : List UInt8) :
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

end SynchronizationTimeMessage

/-- Logon Message: 19 bytes -/
structure LogonMessage where
  logicalAccessId : BitVec 32
  oePartitionId : BitVec 16
  lastMsgSeqNumOptional : BitVec 32
  softwareProvider : Alpha 8
  queueingIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  encodeUIntLE 4 message.logicalAccessId
    ++ (encodeUIntLE 2 message.oePartitionId
    ++ (encodeUIntLE 4 message.lastMsgSeqNumOptional
    ++ (Alpha.encode message.softwareProvider
    ++ (encodeUInt 1 message.queueingIndicator))))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (logicalAccessId, bytes) ← decodeUIntLE 4 bytes
  let (oePartitionId, bytes) ← decodeUIntLE 2 bytes
  let (lastMsgSeqNumOptional, bytes) ← decodeUIntLE 4 bytes
  let (softwareProvider, bytes) ← Alpha.decode 8 bytes
  let (queueingIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ logicalAccessId, oePartitionId, lastMsgSeqNumOptional, softwareProvider, queueingIndicator }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LogonMessage

/-- Logon Ack Message: 12 bytes -/
structure LogonAckMessage where
  exchangeId : Alpha 8
  lastClMsgSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace LogonAckMessage

def encode (message : LogonAckMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (encodeUIntLE 4 message.lastClMsgSeqNum)

def decode (bytes : List UInt8) : Option (LogonAckMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 8 bytes
  let (lastClMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ exchangeId, lastClMsgSeqNum }, bytes)

@[simp] theorem encode_length (message : LogonAckMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : LogonAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogonAckMessage

/-- Logon Reject Message: 17 bytes -/
structure LogonRejectMessage where
  exchangeId : Alpha 8
  logonRejectCode : BitVec 8
  lastClMsgSeqNum : BitVec 32
  lastMsgSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace LogonRejectMessage

def encode (message : LogonRejectMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (encodeUInt 1 message.logonRejectCode
    ++ (encodeUIntLE 4 message.lastClMsgSeqNum
    ++ (encodeUIntLE 4 message.lastMsgSeqNum)))

def decode (bytes : List UInt8) : Option (LogonRejectMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 8 bytes
  let (logonRejectCode, bytes) ← decodeUInt 1 bytes
  let (lastClMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (lastMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ exchangeId, logonRejectCode, lastClMsgSeqNum, lastMsgSeqNum }, bytes)

@[simp] theorem encode_length (message : LogonRejectMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LogonRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogonRejectMessage

/-- Logout Message: 1 bytes -/
structure LogoutMessage where
  logOutReasonCode : BitVec 8
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  encodeUInt 1 message.logOutReasonCode

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (logOutReasonCode, bytes) ← decodeUInt 1 bytes
  pure ({ logOutReasonCode }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LogoutMessage

/-- Heartbeat Message: 0 bytes -/
structure HeartbeatMessage where
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (_ : HeartbeatMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end HeartbeatMessage

/-- Test Request Message: 0 bytes -/
structure TestRequestMessage where
  deriving DecidableEq, Repr

namespace TestRequestMessage

def encode (_ : TestRequestMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (TestRequestMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : TestRequestMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TestRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end TestRequestMessage

/-- Technical Reject Message: 17 bytes -/
structure TechnicalRejectMessage where
  oegOutToMemberOptional : BitVec 64
  rejectedClientMessageSequenceNumber : BitVec 32
  rejectedMessage : BitVec 8
  errorCode : BitVec 16
  rejectedMessageId : BitVec 16
  deriving DecidableEq, Repr

namespace TechnicalRejectMessage

def encode (message : TechnicalRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.oegOutToMemberOptional
    ++ (encodeUIntLE 4 message.rejectedClientMessageSequenceNumber
    ++ (encodeUInt 1 message.rejectedMessage
    ++ (encodeUIntLE 2 message.errorCode
    ++ (encodeUIntLE 2 message.rejectedMessageId))))

def decode (bytes : List UInt8) : Option (TechnicalRejectMessage × List UInt8) := do
  let (oegOutToMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (rejectedClientMessageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (rejectedMessage, bytes) ← decodeUInt 1 bytes
  let (errorCode, bytes) ← decodeUIntLE 2 bytes
  let (rejectedMessageId, bytes) ← decodeUIntLE 2 bytes
  pure ({ oegOutToMemberOptional, rejectedClientMessageSequenceNumber, rejectedMessage, errorCode, rejectedMessageId }, bytes)

@[simp] theorem encode_length (message : TechnicalRejectMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TechnicalRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TechnicalRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TechnicalRejectMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | newOrderMessage (message : NewOrderMessage) -- 1
  | ackMessage (message : AckMessage) -- 3
  | fillMessage (message : FillMessage) -- 4
  | killMessage (message : KillMessage) -- 5
  | cancelReplaceMessage (message : CancelReplaceMessage) -- 6
  | rejectMessage (message : RejectMessage) -- 7
  | quotesMessage (message : QuotesMessage) -- 8
  | quoteAckMessage (message : QuoteAckMessage) -- 9
  | quoteRequestMessage (message : QuoteRequestMessage) -- 10
  | cancelRequestMessage (message : CancelRequestMessage) -- 12
  | massCancelMessage (message : MassCancelMessage) -- 13
  | massCancelAckMessage (message : MassCancelAckMessage) -- 14
  | openOrderRequestMessage (message : OpenOrderRequestMessage) -- 15
  | ownershipRequestAckMessage (message : OwnershipRequestAckMessage) -- 17
  | ownershipRequestMessage (message : OwnershipRequestMessage) -- 18
  | tradeBustNotificationMessage (message : TradeBustNotificationMessage) -- 19
  | collarBreachConfirmationMessage (message : CollarBreachConfirmationMessage) -- 20
  | priceInputMessage (message : PriceInputMessage) -- 28
  | liquidityProviderCommandMessage (message : LiquidityProviderCommandMessage) -- 32
  | askForQuoteMessage (message : AskForQuoteMessage) -- 33
  | requestForExecutionMessage (message : RequestForExecutionMessage) -- 34
  | rfqNotificationMessage (message : RfqNotificationMessage) -- 35
  | rfqMatchingStatusMessage (message : RfqMatchingStatusMessage) -- 36
  | userNotificationMessage (message : UserNotificationMessage) -- 39
  | declarationEntryMessage (message : DeclarationEntryMessage) -- 40
  | declarationEntryAckMessage (message : DeclarationEntryAckMessage) -- 41
  | declarationNoticeMessage (message : DeclarationNoticeMessage) -- 42
  | declarationCancelAndRefusalMessage (message : DeclarationCancelAndRefusalMessage) -- 43
  | fundPriceInputMessage (message : FundPriceInputMessage) -- 44
  | fundPriceInputAckMessage (message : FundPriceInputAckMessage) -- 45
  | declarationEntryRejectMessage (message : DeclarationEntryRejectMessage) -- 46
  | instrumentSynchronizationListMessage (message : InstrumentSynchronizationListMessage) -- 50
  | synchronizationTimeMessage (message : SynchronizationTimeMessage) -- 51
  | logonMessage (message : LogonMessage) -- 100
  | logonAckMessage (message : LogonAckMessage) -- 101
  | logonRejectMessage (message : LogonRejectMessage) -- 102
  | logoutMessage (message : LogoutMessage) -- 103
  | heartbeatMessage (message : HeartbeatMessage) -- 106
  | testRequestMessage (message : TestRequestMessage) -- 107
  | technicalRejectMessage (message : TechnicalRejectMessage) -- 108
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .newOrderMessage _ => 1
  | .ackMessage _ => 3
  | .fillMessage _ => 4
  | .killMessage _ => 5
  | .cancelReplaceMessage _ => 6
  | .rejectMessage _ => 7
  | .quotesMessage _ => 8
  | .quoteAckMessage _ => 9
  | .quoteRequestMessage _ => 10
  | .cancelRequestMessage _ => 12
  | .massCancelMessage _ => 13
  | .massCancelAckMessage _ => 14
  | .openOrderRequestMessage _ => 15
  | .ownershipRequestAckMessage _ => 17
  | .ownershipRequestMessage _ => 18
  | .tradeBustNotificationMessage _ => 19
  | .collarBreachConfirmationMessage _ => 20
  | .priceInputMessage _ => 28
  | .liquidityProviderCommandMessage _ => 32
  | .askForQuoteMessage _ => 33
  | .requestForExecutionMessage _ => 34
  | .rfqNotificationMessage _ => 35
  | .rfqMatchingStatusMessage _ => 36
  | .userNotificationMessage _ => 39
  | .declarationEntryMessage _ => 40
  | .declarationEntryAckMessage _ => 41
  | .declarationNoticeMessage _ => 42
  | .declarationCancelAndRefusalMessage _ => 43
  | .fundPriceInputMessage _ => 44
  | .fundPriceInputAckMessage _ => 45
  | .declarationEntryRejectMessage _ => 46
  | .instrumentSynchronizationListMessage _ => 50
  | .synchronizationTimeMessage _ => 51
  | .logonMessage _ => 100
  | .logonAckMessage _ => 101
  | .logonRejectMessage _ => 102
  | .logoutMessage _ => 103
  | .heartbeatMessage _ => 106
  | .testRequestMessage _ => 107
  | .technicalRejectMessage _ => 108

def encode : Payload → List UInt8
  | .newOrderMessage message => NewOrderMessage.encode message
  | .ackMessage message => AckMessage.encode message
  | .fillMessage message => FillMessage.encode message
  | .killMessage message => KillMessage.encode message
  | .cancelReplaceMessage message => CancelReplaceMessage.encode message
  | .rejectMessage message => RejectMessage.encode message
  | .quotesMessage message => QuotesMessage.encode message
  | .quoteAckMessage message => QuoteAckMessage.encode message
  | .quoteRequestMessage message => QuoteRequestMessage.encode message
  | .cancelRequestMessage message => CancelRequestMessage.encode message
  | .massCancelMessage message => MassCancelMessage.encode message
  | .massCancelAckMessage message => MassCancelAckMessage.encode message
  | .openOrderRequestMessage message => OpenOrderRequestMessage.encode message
  | .ownershipRequestAckMessage message => OwnershipRequestAckMessage.encode message
  | .ownershipRequestMessage message => OwnershipRequestMessage.encode message
  | .tradeBustNotificationMessage message => TradeBustNotificationMessage.encode message
  | .collarBreachConfirmationMessage message => CollarBreachConfirmationMessage.encode message
  | .priceInputMessage message => PriceInputMessage.encode message
  | .liquidityProviderCommandMessage message => LiquidityProviderCommandMessage.encode message
  | .askForQuoteMessage message => AskForQuoteMessage.encode message
  | .requestForExecutionMessage message => RequestForExecutionMessage.encode message
  | .rfqNotificationMessage message => RfqNotificationMessage.encode message
  | .rfqMatchingStatusMessage message => RfqMatchingStatusMessage.encode message
  | .userNotificationMessage message => UserNotificationMessage.encode message
  | .declarationEntryMessage message => DeclarationEntryMessage.encode message
  | .declarationEntryAckMessage message => DeclarationEntryAckMessage.encode message
  | .declarationNoticeMessage message => DeclarationNoticeMessage.encode message
  | .declarationCancelAndRefusalMessage message => DeclarationCancelAndRefusalMessage.encode message
  | .fundPriceInputMessage message => FundPriceInputMessage.encode message
  | .fundPriceInputAckMessage message => FundPriceInputAckMessage.encode message
  | .declarationEntryRejectMessage message => DeclarationEntryRejectMessage.encode message
  | .instrumentSynchronizationListMessage message => InstrumentSynchronizationListMessage.encode message
  | .synchronizationTimeMessage message => SynchronizationTimeMessage.encode message
  | .logonMessage message => LogonMessage.encode message
  | .logonAckMessage message => LogonAckMessage.encode message
  | .logonRejectMessage message => LogonRejectMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .testRequestMessage message => TestRequestMessage.encode message
  | .technicalRejectMessage message => TechnicalRejectMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 29142 := by
  cases message with
  | newOrderMessage inner =>
    have bound_inner := NewOrderMessage.encode_length_le inner
    simp only [encode]
    omega
  | ackMessage inner =>
    simp only [encode, AckMessage.encode_length]
    omega
  | fillMessage inner =>
    have bound_inner := FillMessage.encode_length_le inner
    simp only [encode]
    omega
  | killMessage inner =>
    simp only [encode, KillMessage.encode_length]
    omega
  | cancelReplaceMessage inner =>
    have bound_inner := CancelReplaceMessage.encode_length_le inner
    simp only [encode]
    omega
  | rejectMessage inner =>
    have bound_inner := RejectMessage.encode_length_le inner
    simp only [encode]
    omega
  | quotesMessage inner =>
    have bound_inner := QuotesMessage.encode_length_le inner
    simp only [encode]
    omega
  | quoteAckMessage inner =>
    have bound_inner := QuoteAckMessage.encode_length_le inner
    simp only [encode]
    omega
  | quoteRequestMessage inner =>
    simp only [encode, QuoteRequestMessage.encode_length]
    omega
  | cancelRequestMessage inner =>
    simp only [encode, CancelRequestMessage.encode_length]
    omega
  | massCancelMessage inner =>
    simp only [encode, MassCancelMessage.encode_length]
    omega
  | massCancelAckMessage inner =>
    simp only [encode, MassCancelAckMessage.encode_length]
    omega
  | openOrderRequestMessage inner =>
    simp only [encode, OpenOrderRequestMessage.encode_length]
    omega
  | ownershipRequestAckMessage inner =>
    simp only [encode, OwnershipRequestAckMessage.encode_length]
    omega
  | ownershipRequestMessage inner =>
    simp only [encode, OwnershipRequestMessage.encode_length]
    omega
  | tradeBustNotificationMessage inner =>
    simp only [encode, TradeBustNotificationMessage.encode_length]
    omega
  | collarBreachConfirmationMessage inner =>
    simp only [encode, CollarBreachConfirmationMessage.encode_length]
    omega
  | priceInputMessage inner =>
    simp only [encode, PriceInputMessage.encode_length]
    omega
  | liquidityProviderCommandMessage inner =>
    simp only [encode, LiquidityProviderCommandMessage.encode_length]
    omega
  | askForQuoteMessage inner =>
    simp only [encode, AskForQuoteMessage.encode_length]
    omega
  | requestForExecutionMessage inner =>
    simp only [encode, RequestForExecutionMessage.encode_length]
    omega
  | rfqNotificationMessage inner =>
    simp only [encode, RfqNotificationMessage.encode_length]
    omega
  | rfqMatchingStatusMessage inner =>
    simp only [encode, RfqMatchingStatusMessage.encode_length]
    omega
  | userNotificationMessage inner =>
    simp only [encode, UserNotificationMessage.encode_length]
    omega
  | declarationEntryMessage inner =>
    simp only [encode, DeclarationEntryMessage.encode_length]
    omega
  | declarationEntryAckMessage inner =>
    simp only [encode, DeclarationEntryAckMessage.encode_length]
    omega
  | declarationNoticeMessage inner =>
    simp only [encode, DeclarationNoticeMessage.encode_length]
    omega
  | declarationCancelAndRefusalMessage inner =>
    simp only [encode, DeclarationCancelAndRefusalMessage.encode_length]
    omega
  | fundPriceInputMessage inner =>
    simp only [encode, FundPriceInputMessage.encode_length]
    omega
  | fundPriceInputAckMessage inner =>
    simp only [encode, FundPriceInputAckMessage.encode_length]
    omega
  | declarationEntryRejectMessage inner =>
    simp only [encode, DeclarationEntryRejectMessage.encode_length]
    omega
  | instrumentSynchronizationListMessage inner =>
    have bound_inner := InstrumentSynchronizationListMessage.encode_length_le inner
    simp only [encode]
    omega
  | synchronizationTimeMessage inner =>
    simp only [encode, SynchronizationTimeMessage.encode_length]
    omega
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logonAckMessage inner =>
    simp only [encode, LogonAckMessage.encode_length]
    omega
  | logonRejectMessage inner =>
    simp only [encode, LogonRejectMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | testRequestMessage inner =>
    simp only [encode, TestRequestMessage.encode_length]
    omega
  | technicalRejectMessage inner =>
    simp only [encode, TechnicalRejectMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (NewOrderMessage.decode bytes).map fun (message, rest) => (.newOrderMessage message, rest)
  else if tag = 3 then (AckMessage.decode bytes).map fun (message, rest) => (.ackMessage message, rest)
  else if tag = 4 then (FillMessage.decode bytes).map fun (message, rest) => (.fillMessage message, rest)
  else if tag = 5 then (KillMessage.decode bytes).map fun (message, rest) => (.killMessage message, rest)
  else if tag = 6 then (CancelReplaceMessage.decode bytes).map fun (message, rest) => (.cancelReplaceMessage message, rest)
  else if tag = 7 then (RejectMessage.decode bytes).map fun (message, rest) => (.rejectMessage message, rest)
  else if tag = 8 then (QuotesMessage.decode bytes).map fun (message, rest) => (.quotesMessage message, rest)
  else if tag = 9 then (QuoteAckMessage.decode bytes).map fun (message, rest) => (.quoteAckMessage message, rest)
  else if tag = 10 then (QuoteRequestMessage.decode bytes).map fun (message, rest) => (.quoteRequestMessage message, rest)
  else if tag = 12 then (CancelRequestMessage.decode bytes).map fun (message, rest) => (.cancelRequestMessage message, rest)
  else if tag = 13 then (MassCancelMessage.decode bytes).map fun (message, rest) => (.massCancelMessage message, rest)
  else if tag = 14 then (MassCancelAckMessage.decode bytes).map fun (message, rest) => (.massCancelAckMessage message, rest)
  else if tag = 15 then (OpenOrderRequestMessage.decode bytes).map fun (message, rest) => (.openOrderRequestMessage message, rest)
  else if tag = 17 then (OwnershipRequestAckMessage.decode bytes).map fun (message, rest) => (.ownershipRequestAckMessage message, rest)
  else if tag = 18 then (OwnershipRequestMessage.decode bytes).map fun (message, rest) => (.ownershipRequestMessage message, rest)
  else if tag = 19 then (TradeBustNotificationMessage.decode bytes).map fun (message, rest) => (.tradeBustNotificationMessage message, rest)
  else if tag = 20 then (CollarBreachConfirmationMessage.decode bytes).map fun (message, rest) => (.collarBreachConfirmationMessage message, rest)
  else if tag = 28 then (PriceInputMessage.decode bytes).map fun (message, rest) => (.priceInputMessage message, rest)
  else if tag = 32 then (LiquidityProviderCommandMessage.decode bytes).map fun (message, rest) => (.liquidityProviderCommandMessage message, rest)
  else if tag = 33 then (AskForQuoteMessage.decode bytes).map fun (message, rest) => (.askForQuoteMessage message, rest)
  else if tag = 34 then (RequestForExecutionMessage.decode bytes).map fun (message, rest) => (.requestForExecutionMessage message, rest)
  else if tag = 35 then (RfqNotificationMessage.decode bytes).map fun (message, rest) => (.rfqNotificationMessage message, rest)
  else if tag = 36 then (RfqMatchingStatusMessage.decode bytes).map fun (message, rest) => (.rfqMatchingStatusMessage message, rest)
  else if tag = 39 then (UserNotificationMessage.decode bytes).map fun (message, rest) => (.userNotificationMessage message, rest)
  else if tag = 40 then (DeclarationEntryMessage.decode bytes).map fun (message, rest) => (.declarationEntryMessage message, rest)
  else if tag = 41 then (DeclarationEntryAckMessage.decode bytes).map fun (message, rest) => (.declarationEntryAckMessage message, rest)
  else if tag = 42 then (DeclarationNoticeMessage.decode bytes).map fun (message, rest) => (.declarationNoticeMessage message, rest)
  else if tag = 43 then (DeclarationCancelAndRefusalMessage.decode bytes).map fun (message, rest) => (.declarationCancelAndRefusalMessage message, rest)
  else if tag = 44 then (FundPriceInputMessage.decode bytes).map fun (message, rest) => (.fundPriceInputMessage message, rest)
  else if tag = 45 then (FundPriceInputAckMessage.decode bytes).map fun (message, rest) => (.fundPriceInputAckMessage message, rest)
  else if tag = 46 then (DeclarationEntryRejectMessage.decode bytes).map fun (message, rest) => (.declarationEntryRejectMessage message, rest)
  else if tag = 50 then (InstrumentSynchronizationListMessage.decode bytes).map fun (message, rest) => (.instrumentSynchronizationListMessage message, rest)
  else if tag = 51 then (SynchronizationTimeMessage.decode bytes).map fun (message, rest) => (.synchronizationTimeMessage message, rest)
  else if tag = 100 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 101 then (LogonAckMessage.decode bytes).map fun (message, rest) => (.logonAckMessage message, rest)
  else if tag = 102 then (LogonRejectMessage.decode bytes).map fun (message, rest) => (.logonRejectMessage message, rest)
  else if tag = 103 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 106 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 107 then (TestRequestMessage.decode bytes).map fun (message, rest) => (.testRequestMessage message, rest)
  else if tag = 108 then (TechnicalRejectMessage.decode bytes).map fun (message, rest) => (.technicalRejectMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  frame : BitVec 16
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.frame
    ++ (encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload)))))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (frame, bytes) ← decodeUIntLE 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ frame, blockLength, schemaId, version, payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 29152 := by
  unfold encode
  cases message.payload with
  | newOrderMessage inner =>
    have bound_inner := NewOrderMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | ackMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AckMessage.encode_length]
    omega
  | fillMessage inner =>
    have bound_inner := FillMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | killMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, KillMessage.encode_length]
    omega
  | cancelReplaceMessage inner =>
    have bound_inner := CancelReplaceMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | rejectMessage inner =>
    have bound_inner := RejectMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | quotesMessage inner =>
    have bound_inner := QuotesMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | quoteAckMessage inner =>
    have bound_inner := QuoteAckMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | quoteRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, QuoteRequestMessage.encode_length]
    omega
  | cancelRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, CancelRequestMessage.encode_length]
    omega
  | massCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MassCancelMessage.encode_length]
    omega
  | massCancelAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MassCancelAckMessage.encode_length]
    omega
  | openOrderRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OpenOrderRequestMessage.encode_length]
    omega
  | ownershipRequestAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OwnershipRequestAckMessage.encode_length]
    omega
  | ownershipRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OwnershipRequestMessage.encode_length]
    omega
  | tradeBustNotificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeBustNotificationMessage.encode_length]
    omega
  | collarBreachConfirmationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, CollarBreachConfirmationMessage.encode_length]
    omega
  | priceInputMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, PriceInputMessage.encode_length]
    omega
  | liquidityProviderCommandMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LiquidityProviderCommandMessage.encode_length]
    omega
  | askForQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AskForQuoteMessage.encode_length]
    omega
  | requestForExecutionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RequestForExecutionMessage.encode_length]
    omega
  | rfqNotificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RfqNotificationMessage.encode_length]
    omega
  | rfqMatchingStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RfqMatchingStatusMessage.encode_length]
    omega
  | userNotificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, UserNotificationMessage.encode_length]
    omega
  | declarationEntryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DeclarationEntryMessage.encode_length]
    omega
  | declarationEntryAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DeclarationEntryAckMessage.encode_length]
    omega
  | declarationNoticeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DeclarationNoticeMessage.encode_length]
    omega
  | declarationCancelAndRefusalMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DeclarationCancelAndRefusalMessage.encode_length]
    omega
  | fundPriceInputMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, FundPriceInputMessage.encode_length]
    omega
  | fundPriceInputAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, FundPriceInputAckMessage.encode_length]
    omega
  | declarationEntryRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DeclarationEntryRejectMessage.encode_length]
    omega
  | instrumentSynchronizationListMessage inner =>
    have bound_inner := InstrumentSynchronizationListMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | synchronizationTimeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SynchronizationTimeMessage.encode_length]
    omega
  | logonMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogonMessage.encode_length]
    omega
  | logonAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogonAckMessage.encode_length]
    omega
  | logonRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogonRejectMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogoutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | testRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TestRequestMessage.encode_length]
    omega
  | technicalRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TechnicalRejectMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
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
  rw [Payload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let message ← decodeAll Message.decode bytes.length bytes
  pure { message }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.EuronextOptiqOrderentrygatewaySbeV13
