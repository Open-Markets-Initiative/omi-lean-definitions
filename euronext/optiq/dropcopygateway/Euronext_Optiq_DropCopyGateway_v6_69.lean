import Omi.Wire

/-!
# Euronext Drop Copy Gateway v6.69

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Phase Qualifier is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Ack Qualifiers is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Dark Execution Instruction is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Execution Instruction is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Mi Fid Indicators is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Trade Qualifier Optional is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Trading Session is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Open Close is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Mi Fid Indicators Optional is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Trade Qualifier is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Execution Instruction Optional is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EuronextOptiqDropcopygatewaySbeV669

/-- Dc Market Status Change Message: 79 bytes -/
structure DcMarketStatusChangeMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  emm : BitVec 8
  eventId : BitVec 64
  phaseId : BitVec 8
  tradingGroupState : BitVec 8
  instrumentState : BitVec 8
  changeType : BitVec 8
  symbolIndex : BitVec 32
  eventTime : BitVec 64
  bookState : BitVec 8
  statusReason : BitVec 8
  phaseQualifier : BitVec 16
  tradingPeriod : BitVec 8
  tradingSide : BitVec 8
  priceLimits : BitVec 8
  quoteSpreadMultiplier : BitVec 8
  orderEntryQualifier : BitVec 8
  session : BitVec 8
  scheduledEvent : BitVec 8
  scheduledEventTime : BitVec 64
  tradingGroupOrderEntryQualifier : BitVec 8
  instrumentOrderEntryQualifier : BitVec 8
  phaseTime : BitVec 64
  contractSymbolIndex : BitVec 32
  priceLimitStyle : BitVec 8
  deriving DecidableEq, Repr

namespace DcMarketStatusChangeMessage

def encode (message : DcMarketStatusChangeMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUInt 1 message.phaseId
    ++ (encodeUInt 1 message.tradingGroupState
    ++ (encodeUInt 1 message.instrumentState
    ++ (encodeUInt 1 message.changeType
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.eventTime
    ++ (encodeUInt 1 message.bookState
    ++ (encodeUInt 1 message.statusReason
    ++ (encodeUIntLE 2 message.phaseQualifier
    ++ (encodeUInt 1 message.tradingPeriod
    ++ (encodeUInt 1 message.tradingSide
    ++ (encodeUInt 1 message.priceLimits
    ++ (encodeUInt 1 message.quoteSpreadMultiplier
    ++ (encodeUInt 1 message.orderEntryQualifier
    ++ (encodeUInt 1 message.session
    ++ (encodeUInt 1 message.scheduledEvent
    ++ (encodeUIntLE 8 message.scheduledEventTime
    ++ (encodeUInt 1 message.tradingGroupOrderEntryQualifier
    ++ (encodeUInt 1 message.instrumentOrderEntryQualifier
    ++ (encodeUIntLE 8 message.phaseTime
    ++ (encodeUIntLE 4 message.contractSymbolIndex
    ++ (encodeUInt 1 message.priceLimitStyle))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (DcMarketStatusChangeMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (phaseId, bytes) ← decodeUInt 1 bytes
  let (tradingGroupState, bytes) ← decodeUInt 1 bytes
  let (instrumentState, bytes) ← decodeUInt 1 bytes
  let (changeType, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (bookState, bytes) ← decodeUInt 1 bytes
  let (statusReason, bytes) ← decodeUInt 1 bytes
  let (phaseQualifier, bytes) ← decodeUIntLE 2 bytes
  let (tradingPeriod, bytes) ← decodeUInt 1 bytes
  let (tradingSide, bytes) ← decodeUInt 1 bytes
  let (priceLimits, bytes) ← decodeUInt 1 bytes
  let (quoteSpreadMultiplier, bytes) ← decodeUInt 1 bytes
  let (orderEntryQualifier, bytes) ← decodeUInt 1 bytes
  let (session, bytes) ← decodeUInt 1 bytes
  let (scheduledEvent, bytes) ← decodeUInt 1 bytes
  let (scheduledEventTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingGroupOrderEntryQualifier, bytes) ← decodeUInt 1 bytes
  let (instrumentOrderEntryQualifier, bytes) ← decodeUInt 1 bytes
  let (phaseTime, bytes) ← decodeUIntLE 8 bytes
  let (contractSymbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (priceLimitStyle, bytes) ← decodeUInt 1 bytes
  pure ({ msgSeqNum, produceTime, consumeTime, emm, eventId, phaseId, tradingGroupState, instrumentState, changeType, symbolIndex, eventTime, bookState, statusReason, phaseQualifier, tradingPeriod, tradingSide, priceLimits, quoteSpreadMultiplier, orderEntryQualifier, session, scheduledEvent, scheduledEventTime, tradingGroupOrderEntryQualifier, instrumentOrderEntryQualifier, phaseTime, contractSymbolIndex, priceLimitStyle }, bytes)

@[simp] theorem encode_length (message : DcMarketStatusChangeMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DcMarketStatusChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : DcMarketStatusChangeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DcMarketStatusChangeMessage

/-- Dc Price Update Message: 67 bytes -/
structure DcPriceUpdateMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  emm : BitVec 8
  eventId : BitVec 64
  eventTime : BitVec 64
  priceType : BitVec 8
  symbolIndex : BitVec 32
  priceOptional : BitVec 64
  quantityOptional : BitVec 64
  imbalanceQty : BitVec 64
  imbalanceQtySide : BitVec 8
  deriving DecidableEq, Repr

namespace DcPriceUpdateMessage

def encode (message : DcPriceUpdateMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUIntLE 8 message.eventTime
    ++ (encodeUInt 1 message.priceType
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.quantityOptional
    ++ (encodeUIntLE 8 message.imbalanceQty
    ++ (encodeUInt 1 message.imbalanceQtySide)))))))))))

def decode (bytes : List UInt8) : Option (DcPriceUpdateMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (priceType, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (quantityOptional, bytes) ← decodeUIntLE 8 bytes
  let (imbalanceQty, bytes) ← decodeUIntLE 8 bytes
  let (imbalanceQtySide, bytes) ← decodeUInt 1 bytes
  pure ({ msgSeqNum, produceTime, consumeTime, emm, eventId, eventTime, priceType, symbolIndex, priceOptional, quantityOptional, imbalanceQty, imbalanceQtySide }, bytes)

@[simp] theorem encode_length (message : DcPriceUpdateMessage) : (encode message).length = 67 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DcPriceUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcPriceUpdateMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DcPriceUpdateMessage

/-- Long Order Free Text Section Group: 18 bytes -/
structure LongOrderFreeTextSectionGroup where
  freeText : Alpha 18
  deriving DecidableEq, Repr

namespace LongOrderFreeTextSectionGroup

def encode (message : LongOrderFreeTextSectionGroup) : List UInt8 :=
  Alpha.encode message.freeText

def decode (bytes : List UInt8) : Option (LongOrderFreeTextSectionGroup × List UInt8) := do
  let (freeText, bytes) ← Alpha.decode 18 bytes
  pure ({ freeText }, bytes)

@[simp] theorem encode_length (message : LongOrderFreeTextSectionGroup) : (encode message).length = 18 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LongOrderFreeTextSectionGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderFreeTextSectionGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LongOrderFreeTextSectionGroup

/-- Long Order Free Text Section Groups -/
structure LongOrderFreeTextSectionGroups where
  blockLengthShort : BitVec 8
  longOrderFreeTextSectionGroup : Bounded 1 LongOrderFreeTextSectionGroup
  deriving DecidableEq, Repr

namespace LongOrderFreeTextSectionGroups

def encode (message : LongOrderFreeTextSectionGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderFreeTextSectionGroup.val.length)
    ++ (encodeMany LongOrderFreeTextSectionGroup.encode message.longOrderFreeTextSectionGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderFreeTextSectionGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderFreeTextSectionGroup_, bytes) ← decodeMany LongOrderFreeTextSectionGroup.decode numInGroup.toNat bytes
  if fits_longOrderFreeTextSectionGroup : longOrderFreeTextSectionGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderFreeTextSectionGroup := ⟨longOrderFreeTextSectionGroup_, fits_longOrderFreeTextSectionGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderFreeTextSectionGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderFreeTextSectionGroups) : (encode message).length ≤ 4592 := by
  have bound_longOrderFreeTextSectionGroup := message.longOrderFreeTextSectionGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderFreeTextSectionGroup.encode 18 LongOrderFreeTextSectionGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderFreeTextSectionGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderFreeTextSectionGroup.encode LongOrderFreeTextSectionGroup.decode LongOrderFreeTextSectionGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderFreeTextSectionGroup.length_lt]
  rfl

end LongOrderFreeTextSectionGroups

/-- Long Order Optional Fields Group: 34 bytes -/
structure LongOrderOptionalFieldsGroup where
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

namespace LongOrderOptionalFieldsGroup

def encode (message : LongOrderOptionalFieldsGroup) : List UInt8 :=
  encodeUIntLE 8 message.stopPx
    ++ (encodeUInt 1 message.pegOffset
    ++ (encodeUIntLE 8 message.undisclosedPrice
    ++ (encodeUIntLE 8 message.disclosedQty
    ++ (encodeUIntLE 4 message.orderExpirationTime
    ++ (encodeUIntLE 2 message.orderExpirationDate
    ++ (encodeUIntLE 1 message.tradingSession
    ++ (encodeUInt 1 message.stopTriggeredTimeInForce
    ++ (encodeUInt 1 message.undisclosedIcebergType))))))))

def decode (bytes : List UInt8) : Option (LongOrderOptionalFieldsGroup × List UInt8) := do
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

@[simp] theorem encode_length (message : LongOrderOptionalFieldsGroup) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LongOrderOptionalFieldsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderOptionalFieldsGroup) (rest : List UInt8) :
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

end LongOrderOptionalFieldsGroup

/-- Long Order Optional Fields Groups -/
structure LongOrderOptionalFieldsGroups where
  blockLengthShort : BitVec 8
  longOrderOptionalFieldsGroup : Bounded 1 LongOrderOptionalFieldsGroup
  deriving DecidableEq, Repr

namespace LongOrderOptionalFieldsGroups

def encode (message : LongOrderOptionalFieldsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderOptionalFieldsGroup.val.length)
    ++ (encodeMany LongOrderOptionalFieldsGroup.encode message.longOrderOptionalFieldsGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderOptionalFieldsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderOptionalFieldsGroup_, bytes) ← decodeMany LongOrderOptionalFieldsGroup.decode numInGroup.toNat bytes
  if fits_longOrderOptionalFieldsGroup : longOrderOptionalFieldsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderOptionalFieldsGroup := ⟨longOrderOptionalFieldsGroup_, fits_longOrderOptionalFieldsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderOptionalFieldsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderOptionalFieldsGroups) : (encode message).length ≤ 8672 := by
  have bound_longOrderOptionalFieldsGroup := message.longOrderOptionalFieldsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderOptionalFieldsGroup.encode 34 LongOrderOptionalFieldsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderOptionalFieldsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderOptionalFieldsGroup.encode LongOrderOptionalFieldsGroup.decode LongOrderOptionalFieldsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderOptionalFieldsGroup.length_lt]
  rfl

end LongOrderOptionalFieldsGroups

/-- Long Order Clearing Fields Group: 33 bytes -/
structure LongOrderClearingFieldsGroup where
  clearingFirmIdOptional : Alpha 8
  clientId : Alpha 8
  accountNumber : Alpha 12
  technicalOrigin : BitVec 8
  openClose : BitVec 16
  clearingInstructionOptional : BitVec 16
  deriving DecidableEq, Repr

namespace LongOrderClearingFieldsGroup

def encode (message : LongOrderClearingFieldsGroup) : List UInt8 :=
  Alpha.encode message.clearingFirmIdOptional
    ++ (Alpha.encode message.clientId
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 1 message.technicalOrigin
    ++ (encodeUIntLE 2 message.openClose
    ++ (encodeUIntLE 2 message.clearingInstructionOptional)))))

def decode (bytes : List UInt8) : Option (LongOrderClearingFieldsGroup × List UInt8) := do
  let (clearingFirmIdOptional, bytes) ← Alpha.decode 8 bytes
  let (clientId, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 12 bytes
  let (technicalOrigin, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUIntLE 2 bytes
  let (clearingInstructionOptional, bytes) ← decodeUIntLE 2 bytes
  pure ({ clearingFirmIdOptional, clientId, accountNumber, technicalOrigin, openClose, clearingInstructionOptional }, bytes)

@[simp] theorem encode_length (message : LongOrderClearingFieldsGroup) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LongOrderClearingFieldsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderClearingFieldsGroup) (rest : List UInt8) :
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

end LongOrderClearingFieldsGroup

/-- Long Order Clearing Fields Groups -/
structure LongOrderClearingFieldsGroups where
  blockLengthShort : BitVec 8
  longOrderClearingFieldsGroup : Bounded 1 LongOrderClearingFieldsGroup
  deriving DecidableEq, Repr

namespace LongOrderClearingFieldsGroups

def encode (message : LongOrderClearingFieldsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderClearingFieldsGroup.val.length)
    ++ (encodeMany LongOrderClearingFieldsGroup.encode message.longOrderClearingFieldsGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderClearingFieldsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderClearingFieldsGroup_, bytes) ← decodeMany LongOrderClearingFieldsGroup.decode numInGroup.toNat bytes
  if fits_longOrderClearingFieldsGroup : longOrderClearingFieldsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderClearingFieldsGroup := ⟨longOrderClearingFieldsGroup_, fits_longOrderClearingFieldsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderClearingFieldsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderClearingFieldsGroups) : (encode message).length ≤ 8417 := by
  have bound_longOrderClearingFieldsGroup := message.longOrderClearingFieldsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderClearingFieldsGroup.encode 33 LongOrderClearingFieldsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderClearingFieldsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderClearingFieldsGroup.encode LongOrderClearingFieldsGroup.decode LongOrderClearingFieldsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderClearingFieldsGroup.length_lt]
  rfl

end LongOrderClearingFieldsGroups

/-- Long Order Non Modifiable Opt Fields Group: 10 bytes -/
structure LongOrderNonModifiableOptFieldsGroup where
  tradingCapacityOptional : BitVec 8
  minimumOrderQuantity : BitVec 64
  accountTypeCross : BitVec 8
  deriving DecidableEq, Repr

namespace LongOrderNonModifiableOptFieldsGroup

def encode (message : LongOrderNonModifiableOptFieldsGroup) : List UInt8 :=
  encodeUInt 1 message.tradingCapacityOptional
    ++ (encodeUIntLE 8 message.minimumOrderQuantity
    ++ (encodeUInt 1 message.accountTypeCross))

def decode (bytes : List UInt8) : Option (LongOrderNonModifiableOptFieldsGroup × List UInt8) := do
  let (tradingCapacityOptional, bytes) ← decodeUInt 1 bytes
  let (minimumOrderQuantity, bytes) ← decodeUIntLE 8 bytes
  let (accountTypeCross, bytes) ← decodeUInt 1 bytes
  pure ({ tradingCapacityOptional, minimumOrderQuantity, accountTypeCross }, bytes)

@[simp] theorem encode_length (message : LongOrderNonModifiableOptFieldsGroup) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LongOrderNonModifiableOptFieldsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderNonModifiableOptFieldsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LongOrderNonModifiableOptFieldsGroup

/-- Long Order Non Modifiable Opt Fields Groups -/
structure LongOrderNonModifiableOptFieldsGroups where
  blockLengthShort : BitVec 8
  longOrderNonModifiableOptFieldsGroup : Bounded 1 LongOrderNonModifiableOptFieldsGroup
  deriving DecidableEq, Repr

namespace LongOrderNonModifiableOptFieldsGroups

def encode (message : LongOrderNonModifiableOptFieldsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderNonModifiableOptFieldsGroup.val.length)
    ++ (encodeMany LongOrderNonModifiableOptFieldsGroup.encode message.longOrderNonModifiableOptFieldsGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderNonModifiableOptFieldsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderNonModifiableOptFieldsGroup_, bytes) ← decodeMany LongOrderNonModifiableOptFieldsGroup.decode numInGroup.toNat bytes
  if fits_longOrderNonModifiableOptFieldsGroup : longOrderNonModifiableOptFieldsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderNonModifiableOptFieldsGroup := ⟨longOrderNonModifiableOptFieldsGroup_, fits_longOrderNonModifiableOptFieldsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderNonModifiableOptFieldsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderNonModifiableOptFieldsGroups) : (encode message).length ≤ 2552 := by
  have bound_longOrderNonModifiableOptFieldsGroup := message.longOrderNonModifiableOptFieldsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderNonModifiableOptFieldsGroup.encode 10 LongOrderNonModifiableOptFieldsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderNonModifiableOptFieldsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderNonModifiableOptFieldsGroup.encode LongOrderNonModifiableOptFieldsGroup.decode LongOrderNonModifiableOptFieldsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderNonModifiableOptFieldsGroup.length_lt]
  rfl

end LongOrderNonModifiableOptFieldsGroups

/-- Long Order Non Modifiable Short Codes Group: 16 bytes -/
structure LongOrderNonModifiableShortCodesGroup where
  originalClientIdShortCode : BitVec 32
  originalExecWFirmShortCode : BitVec 32
  originalInvestDecisWFirmShortCode : BitVec 32
  originalNonExecBrokerShortCode : BitVec 32
  deriving DecidableEq, Repr

namespace LongOrderNonModifiableShortCodesGroup

def encode (message : LongOrderNonModifiableShortCodesGroup) : List UInt8 :=
  encodeUIntLE 4 message.originalClientIdShortCode
    ++ (encodeUIntLE 4 message.originalExecWFirmShortCode
    ++ (encodeUIntLE 4 message.originalInvestDecisWFirmShortCode
    ++ (encodeUIntLE 4 message.originalNonExecBrokerShortCode)))

def decode (bytes : List UInt8) : Option (LongOrderNonModifiableShortCodesGroup × List UInt8) := do
  let (originalClientIdShortCode, bytes) ← decodeUIntLE 4 bytes
  let (originalExecWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (originalInvestDecisWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (originalNonExecBrokerShortCode, bytes) ← decodeUIntLE 4 bytes
  pure ({ originalClientIdShortCode, originalExecWFirmShortCode, originalInvestDecisWFirmShortCode, originalNonExecBrokerShortCode }, bytes)

@[simp] theorem encode_length (message : LongOrderNonModifiableShortCodesGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LongOrderNonModifiableShortCodesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderNonModifiableShortCodesGroup) (rest : List UInt8) :
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

end LongOrderNonModifiableShortCodesGroup

/-- Long Order Non Modifiable Short Codes Groups -/
structure LongOrderNonModifiableShortCodesGroups where
  blockLengthShort : BitVec 8
  longOrderNonModifiableShortCodesGroup : Bounded 1 LongOrderNonModifiableShortCodesGroup
  deriving DecidableEq, Repr

namespace LongOrderNonModifiableShortCodesGroups

def encode (message : LongOrderNonModifiableShortCodesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderNonModifiableShortCodesGroup.val.length)
    ++ (encodeMany LongOrderNonModifiableShortCodesGroup.encode message.longOrderNonModifiableShortCodesGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderNonModifiableShortCodesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderNonModifiableShortCodesGroup_, bytes) ← decodeMany LongOrderNonModifiableShortCodesGroup.decode numInGroup.toNat bytes
  if fits_longOrderNonModifiableShortCodesGroup : longOrderNonModifiableShortCodesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderNonModifiableShortCodesGroup := ⟨longOrderNonModifiableShortCodesGroup_, fits_longOrderNonModifiableShortCodesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderNonModifiableShortCodesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderNonModifiableShortCodesGroups) : (encode message).length ≤ 4082 := by
  have bound_longOrderNonModifiableShortCodesGroup := message.longOrderNonModifiableShortCodesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderNonModifiableShortCodesGroup.encode 16 LongOrderNonModifiableShortCodesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderNonModifiableShortCodesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderNonModifiableShortCodesGroup.encode LongOrderNonModifiableShortCodesGroup.decode LongOrderNonModifiableShortCodesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderNonModifiableShortCodesGroup.length_lt]
  rfl

end LongOrderNonModifiableShortCodesGroups

/-- Long Order Modifiable Short Codes Group: 8 bytes -/
structure LongOrderModifiableShortCodesGroup where
  eventClientIdShortCode : BitVec 32
  eventExecWFirmShortCode : BitVec 32
  deriving DecidableEq, Repr

namespace LongOrderModifiableShortCodesGroup

def encode (message : LongOrderModifiableShortCodesGroup) : List UInt8 :=
  encodeUIntLE 4 message.eventClientIdShortCode
    ++ (encodeUIntLE 4 message.eventExecWFirmShortCode)

def decode (bytes : List UInt8) : Option (LongOrderModifiableShortCodesGroup × List UInt8) := do
  let (eventClientIdShortCode, bytes) ← decodeUIntLE 4 bytes
  let (eventExecWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  pure ({ eventClientIdShortCode, eventExecWFirmShortCode }, bytes)

@[simp] theorem encode_length (message : LongOrderModifiableShortCodesGroup) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LongOrderModifiableShortCodesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderModifiableShortCodesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LongOrderModifiableShortCodesGroup

/-- Long Order Modifiable Short Codes Groups -/
structure LongOrderModifiableShortCodesGroups where
  blockLengthShort : BitVec 8
  longOrderModifiableShortCodesGroup : Bounded 1 LongOrderModifiableShortCodesGroup
  deriving DecidableEq, Repr

namespace LongOrderModifiableShortCodesGroups

def encode (message : LongOrderModifiableShortCodesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderModifiableShortCodesGroup.val.length)
    ++ (encodeMany LongOrderModifiableShortCodesGroup.encode message.longOrderModifiableShortCodesGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderModifiableShortCodesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderModifiableShortCodesGroup_, bytes) ← decodeMany LongOrderModifiableShortCodesGroup.decode numInGroup.toNat bytes
  if fits_longOrderModifiableShortCodesGroup : longOrderModifiableShortCodesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderModifiableShortCodesGroup := ⟨longOrderModifiableShortCodesGroup_, fits_longOrderModifiableShortCodesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderModifiableShortCodesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderModifiableShortCodesGroups) : (encode message).length ≤ 2042 := by
  have bound_longOrderModifiableShortCodesGroup := message.longOrderModifiableShortCodesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderModifiableShortCodesGroup.encode 8 LongOrderModifiableShortCodesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderModifiableShortCodesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderModifiableShortCodesGroup.encode LongOrderModifiableShortCodesGroup.decode LongOrderModifiableShortCodesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderModifiableShortCodesGroup.length_lt]
  rfl

end LongOrderModifiableShortCodesGroups

/-- Long Order Commercial Fields Group: 41 bytes -/
structure LongOrderCommercialFieldsGroup where
  marketPhaseFlag : BitVec 8
  marginTradingFlag : BitVec 8
  accessFlag : BitVec 8
  traderId : Alpha 16
  senderLocationId : Alpha 11
  deskId : Alpha 11
  deriving DecidableEq, Repr

namespace LongOrderCommercialFieldsGroup

def encode (message : LongOrderCommercialFieldsGroup) : List UInt8 :=
  encodeUInt 1 message.marketPhaseFlag
    ++ (encodeUInt 1 message.marginTradingFlag
    ++ (encodeUInt 1 message.accessFlag
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.senderLocationId
    ++ (Alpha.encode message.deskId)))))

def decode (bytes : List UInt8) : Option (LongOrderCommercialFieldsGroup × List UInt8) := do
  let (marketPhaseFlag, bytes) ← decodeUInt 1 bytes
  let (marginTradingFlag, bytes) ← decodeUInt 1 bytes
  let (accessFlag, bytes) ← decodeUInt 1 bytes
  let (traderId, bytes) ← Alpha.decode 16 bytes
  let (senderLocationId, bytes) ← Alpha.decode 11 bytes
  let (deskId, bytes) ← Alpha.decode 11 bytes
  pure ({ marketPhaseFlag, marginTradingFlag, accessFlag, traderId, senderLocationId, deskId }, bytes)

@[simp] theorem encode_length (message : LongOrderCommercialFieldsGroup) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LongOrderCommercialFieldsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderCommercialFieldsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end LongOrderCommercialFieldsGroup

/-- Long Order Commercial Fields Groups -/
structure LongOrderCommercialFieldsGroups where
  blockLengthShort : BitVec 8
  longOrderCommercialFieldsGroup : Bounded 1 LongOrderCommercialFieldsGroup
  deriving DecidableEq, Repr

namespace LongOrderCommercialFieldsGroups

def encode (message : LongOrderCommercialFieldsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderCommercialFieldsGroup.val.length)
    ++ (encodeMany LongOrderCommercialFieldsGroup.encode message.longOrderCommercialFieldsGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderCommercialFieldsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderCommercialFieldsGroup_, bytes) ← decodeMany LongOrderCommercialFieldsGroup.decode numInGroup.toNat bytes
  if fits_longOrderCommercialFieldsGroup : longOrderCommercialFieldsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderCommercialFieldsGroup := ⟨longOrderCommercialFieldsGroup_, fits_longOrderCommercialFieldsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderCommercialFieldsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderCommercialFieldsGroups) : (encode message).length ≤ 10457 := by
  have bound_longOrderCommercialFieldsGroup := message.longOrderCommercialFieldsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderCommercialFieldsGroup.encode 41 LongOrderCommercialFieldsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderCommercialFieldsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderCommercialFieldsGroup.encode LongOrderCommercialFieldsGroup.decode LongOrderCommercialFieldsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderCommercialFieldsGroup.length_lt]
  rfl

end LongOrderCommercialFieldsGroups

/-- Long Order Modifiable Commercial Investor Field Group: 16 bytes -/
structure LongOrderModifiableCommercialInvestorFieldGroup where
  eventInvestorId : Alpha 16
  deriving DecidableEq, Repr

namespace LongOrderModifiableCommercialInvestorFieldGroup

def encode (message : LongOrderModifiableCommercialInvestorFieldGroup) : List UInt8 :=
  Alpha.encode message.eventInvestorId

def decode (bytes : List UInt8) : Option (LongOrderModifiableCommercialInvestorFieldGroup × List UInt8) := do
  let (eventInvestorId, bytes) ← Alpha.decode 16 bytes
  pure ({ eventInvestorId }, bytes)

@[simp] theorem encode_length (message : LongOrderModifiableCommercialInvestorFieldGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LongOrderModifiableCommercialInvestorFieldGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderModifiableCommercialInvestorFieldGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LongOrderModifiableCommercialInvestorFieldGroup

/-- Long Order Modifiable Commercial Investor Field Groups -/
structure LongOrderModifiableCommercialInvestorFieldGroups where
  blockLengthShort : BitVec 8
  longOrderModifiableCommercialInvestorFieldGroup : Bounded 1 LongOrderModifiableCommercialInvestorFieldGroup
  deriving DecidableEq, Repr

namespace LongOrderModifiableCommercialInvestorFieldGroups

def encode (message : LongOrderModifiableCommercialInvestorFieldGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderModifiableCommercialInvestorFieldGroup.val.length)
    ++ (encodeMany LongOrderModifiableCommercialInvestorFieldGroup.encode message.longOrderModifiableCommercialInvestorFieldGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderModifiableCommercialInvestorFieldGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderModifiableCommercialInvestorFieldGroup_, bytes) ← decodeMany LongOrderModifiableCommercialInvestorFieldGroup.decode numInGroup.toNat bytes
  if fits_longOrderModifiableCommercialInvestorFieldGroup : longOrderModifiableCommercialInvestorFieldGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderModifiableCommercialInvestorFieldGroup := ⟨longOrderModifiableCommercialInvestorFieldGroup_, fits_longOrderModifiableCommercialInvestorFieldGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderModifiableCommercialInvestorFieldGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderModifiableCommercialInvestorFieldGroups) : (encode message).length ≤ 4082 := by
  have bound_longOrderModifiableCommercialInvestorFieldGroup := message.longOrderModifiableCommercialInvestorFieldGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderModifiableCommercialInvestorFieldGroup.encode 16 LongOrderModifiableCommercialInvestorFieldGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderModifiableCommercialInvestorFieldGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderModifiableCommercialInvestorFieldGroup.encode LongOrderModifiableCommercialInvestorFieldGroup.decode LongOrderModifiableCommercialInvestorFieldGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderModifiableCommercialInvestorFieldGroup.length_lt]
  rfl

end LongOrderModifiableCommercialInvestorFieldGroups

/-- Long Order Non Modifiable Commercial Investor Field Group: 16 bytes -/
structure LongOrderNonModifiableCommercialInvestorFieldGroup where
  originalInvestorId : Alpha 16
  deriving DecidableEq, Repr

namespace LongOrderNonModifiableCommercialInvestorFieldGroup

def encode (message : LongOrderNonModifiableCommercialInvestorFieldGroup) : List UInt8 :=
  Alpha.encode message.originalInvestorId

def decode (bytes : List UInt8) : Option (LongOrderNonModifiableCommercialInvestorFieldGroup × List UInt8) := do
  let (originalInvestorId, bytes) ← Alpha.decode 16 bytes
  pure ({ originalInvestorId }, bytes)

@[simp] theorem encode_length (message : LongOrderNonModifiableCommercialInvestorFieldGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LongOrderNonModifiableCommercialInvestorFieldGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderNonModifiableCommercialInvestorFieldGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LongOrderNonModifiableCommercialInvestorFieldGroup

/-- Long Order Non Modifiable Commercial Investor Field Groups -/
structure LongOrderNonModifiableCommercialInvestorFieldGroups where
  blockLengthShort : BitVec 8
  longOrderNonModifiableCommercialInvestorFieldGroup : Bounded 1 LongOrderNonModifiableCommercialInvestorFieldGroup
  deriving DecidableEq, Repr

namespace LongOrderNonModifiableCommercialInvestorFieldGroups

def encode (message : LongOrderNonModifiableCommercialInvestorFieldGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderNonModifiableCommercialInvestorFieldGroup.val.length)
    ++ (encodeMany LongOrderNonModifiableCommercialInvestorFieldGroup.encode message.longOrderNonModifiableCommercialInvestorFieldGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderNonModifiableCommercialInvestorFieldGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderNonModifiableCommercialInvestorFieldGroup_, bytes) ← decodeMany LongOrderNonModifiableCommercialInvestorFieldGroup.decode numInGroup.toNat bytes
  if fits_longOrderNonModifiableCommercialInvestorFieldGroup : longOrderNonModifiableCommercialInvestorFieldGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderNonModifiableCommercialInvestorFieldGroup := ⟨longOrderNonModifiableCommercialInvestorFieldGroup_, fits_longOrderNonModifiableCommercialInvestorFieldGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderNonModifiableCommercialInvestorFieldGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderNonModifiableCommercialInvestorFieldGroups) : (encode message).length ≤ 4082 := by
  have bound_longOrderNonModifiableCommercialInvestorFieldGroup := message.longOrderNonModifiableCommercialInvestorFieldGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderNonModifiableCommercialInvestorFieldGroup.encode 16 LongOrderNonModifiableCommercialInvestorFieldGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderNonModifiableCommercialInvestorFieldGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderNonModifiableCommercialInvestorFieldGroup.encode LongOrderNonModifiableCommercialInvestorFieldGroup.decode LongOrderNonModifiableCommercialInvestorFieldGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderNonModifiableCommercialInvestorFieldGroup.length_lt]
  rfl

end LongOrderNonModifiableCommercialInvestorFieldGroups

/-- Long Order Extended Clearing Account Group: 16 bytes -/
structure LongOrderExtendedClearingAccountGroup where
  clearingAccount : Alpha 16
  deriving DecidableEq, Repr

namespace LongOrderExtendedClearingAccountGroup

def encode (message : LongOrderExtendedClearingAccountGroup) : List UInt8 :=
  Alpha.encode message.clearingAccount

def decode (bytes : List UInt8) : Option (LongOrderExtendedClearingAccountGroup × List UInt8) := do
  let (clearingAccount, bytes) ← Alpha.decode 16 bytes
  pure ({ clearingAccount }, bytes)

@[simp] theorem encode_length (message : LongOrderExtendedClearingAccountGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LongOrderExtendedClearingAccountGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderExtendedClearingAccountGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LongOrderExtendedClearingAccountGroup

/-- Long Order Extended Clearing Account Groups -/
structure LongOrderExtendedClearingAccountGroups where
  blockLengthShort : BitVec 8
  longOrderExtendedClearingAccountGroup : Bounded 1 LongOrderExtendedClearingAccountGroup
  deriving DecidableEq, Repr

namespace LongOrderExtendedClearingAccountGroups

def encode (message : LongOrderExtendedClearingAccountGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderExtendedClearingAccountGroup.val.length)
    ++ (encodeMany LongOrderExtendedClearingAccountGroup.encode message.longOrderExtendedClearingAccountGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderExtendedClearingAccountGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderExtendedClearingAccountGroup_, bytes) ← decodeMany LongOrderExtendedClearingAccountGroup.decode numInGroup.toNat bytes
  if fits_longOrderExtendedClearingAccountGroup : longOrderExtendedClearingAccountGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderExtendedClearingAccountGroup := ⟨longOrderExtendedClearingAccountGroup_, fits_longOrderExtendedClearingAccountGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderExtendedClearingAccountGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderExtendedClearingAccountGroups) : (encode message).length ≤ 4082 := by
  have bound_longOrderExtendedClearingAccountGroup := message.longOrderExtendedClearingAccountGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderExtendedClearingAccountGroup.encode 16 LongOrderExtendedClearingAccountGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderExtendedClearingAccountGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderExtendedClearingAccountGroup.encode LongOrderExtendedClearingAccountGroup.decode LongOrderExtendedClearingAccountGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderExtendedClearingAccountGroup.length_lt]
  rfl

end LongOrderExtendedClearingAccountGroups

/-- Long Order Strategy Fields Group: 41 bytes -/
structure LongOrderStrategyFieldsGroup where
  legLastPx : BitVec 64
  legLastQty : BitVec 64
  legInstrumentId : BitVec 32
  legSide : BitVec 8
  executionIdOptional : BitVec 32
  tradeUniqueIdentifier : Alpha 16
  deriving DecidableEq, Repr

namespace LongOrderStrategyFieldsGroup

def encode (message : LongOrderStrategyFieldsGroup) : List UInt8 :=
  encodeUIntLE 8 message.legLastPx
    ++ (encodeUIntLE 8 message.legLastQty
    ++ (encodeUIntLE 4 message.legInstrumentId
    ++ (encodeUInt 1 message.legSide
    ++ (encodeUIntLE 4 message.executionIdOptional
    ++ (Alpha.encode message.tradeUniqueIdentifier)))))

def decode (bytes : List UInt8) : Option (LongOrderStrategyFieldsGroup × List UInt8) := do
  let (legLastPx, bytes) ← decodeUIntLE 8 bytes
  let (legLastQty, bytes) ← decodeUIntLE 8 bytes
  let (legInstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (executionIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (tradeUniqueIdentifier, bytes) ← Alpha.decode 16 bytes
  pure ({ legLastPx, legLastQty, legInstrumentId, legSide, executionIdOptional, tradeUniqueIdentifier }, bytes)

@[simp] theorem encode_length (message : LongOrderStrategyFieldsGroup) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LongOrderStrategyFieldsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderStrategyFieldsGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LongOrderStrategyFieldsGroup

/-- Long Order Strategy Fields Groups -/
structure LongOrderStrategyFieldsGroups where
  blockLengthShort : BitVec 8
  longOrderStrategyFieldsGroup : Bounded 1 LongOrderStrategyFieldsGroup
  deriving DecidableEq, Repr

namespace LongOrderStrategyFieldsGroups

def encode (message : LongOrderStrategyFieldsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderStrategyFieldsGroup.val.length)
    ++ (encodeMany LongOrderStrategyFieldsGroup.encode message.longOrderStrategyFieldsGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderStrategyFieldsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderStrategyFieldsGroup_, bytes) ← decodeMany LongOrderStrategyFieldsGroup.decode numInGroup.toNat bytes
  if fits_longOrderStrategyFieldsGroup : longOrderStrategyFieldsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderStrategyFieldsGroup := ⟨longOrderStrategyFieldsGroup_, fits_longOrderStrategyFieldsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderStrategyFieldsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderStrategyFieldsGroups) : (encode message).length ≤ 10457 := by
  have bound_longOrderStrategyFieldsGroup := message.longOrderStrategyFieldsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderStrategyFieldsGroup.encode 41 LongOrderStrategyFieldsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderStrategyFieldsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderStrategyFieldsGroup.encode LongOrderStrategyFieldsGroup.decode LongOrderStrategyFieldsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderStrategyFieldsGroup.length_lt]
  rfl

end LongOrderStrategyFieldsGroups

/-- Long Order Optional Fields Derivatives Group: 17 bytes -/
structure LongOrderOptionalFieldsDerivativesGroup where
  evaluatedPrice : BitVec 64
  messagePriceNotation : BitVec 8
  finalSymbolIndex : BitVec 32
  finalExecutionId : BitVec 32
  deriving DecidableEq, Repr

namespace LongOrderOptionalFieldsDerivativesGroup

def encode (message : LongOrderOptionalFieldsDerivativesGroup) : List UInt8 :=
  encodeUIntLE 8 message.evaluatedPrice
    ++ (encodeUInt 1 message.messagePriceNotation
    ++ (encodeUIntLE 4 message.finalSymbolIndex
    ++ (encodeUIntLE 4 message.finalExecutionId)))

def decode (bytes : List UInt8) : Option (LongOrderOptionalFieldsDerivativesGroup × List UInt8) := do
  let (evaluatedPrice, bytes) ← decodeUIntLE 8 bytes
  let (messagePriceNotation, bytes) ← decodeUInt 1 bytes
  let (finalSymbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (finalExecutionId, bytes) ← decodeUIntLE 4 bytes
  pure ({ evaluatedPrice, messagePriceNotation, finalSymbolIndex, finalExecutionId }, bytes)

@[simp] theorem encode_length (message : LongOrderOptionalFieldsDerivativesGroup) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LongOrderOptionalFieldsDerivativesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderOptionalFieldsDerivativesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LongOrderOptionalFieldsDerivativesGroup

/-- Long Order Optional Fields Derivatives Groups -/
structure LongOrderOptionalFieldsDerivativesGroups where
  blockLengthShort : BitVec 8
  longOrderOptionalFieldsDerivativesGroup : Bounded 1 LongOrderOptionalFieldsDerivativesGroup
  deriving DecidableEq, Repr

namespace LongOrderOptionalFieldsDerivativesGroups

def encode (message : LongOrderOptionalFieldsDerivativesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderOptionalFieldsDerivativesGroup.val.length)
    ++ (encodeMany LongOrderOptionalFieldsDerivativesGroup.encode message.longOrderOptionalFieldsDerivativesGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderOptionalFieldsDerivativesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderOptionalFieldsDerivativesGroup_, bytes) ← decodeMany LongOrderOptionalFieldsDerivativesGroup.decode numInGroup.toNat bytes
  if fits_longOrderOptionalFieldsDerivativesGroup : longOrderOptionalFieldsDerivativesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderOptionalFieldsDerivativesGroup := ⟨longOrderOptionalFieldsDerivativesGroup_, fits_longOrderOptionalFieldsDerivativesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderOptionalFieldsDerivativesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderOptionalFieldsDerivativesGroups) : (encode message).length ≤ 4337 := by
  have bound_longOrderOptionalFieldsDerivativesGroup := message.longOrderOptionalFieldsDerivativesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderOptionalFieldsDerivativesGroup.encode 17 LongOrderOptionalFieldsDerivativesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderOptionalFieldsDerivativesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderOptionalFieldsDerivativesGroup.encode LongOrderOptionalFieldsDerivativesGroup.decode LongOrderOptionalFieldsDerivativesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderOptionalFieldsDerivativesGroup.length_lt]
  rfl

end LongOrderOptionalFieldsDerivativesGroups

/-- Long Order Additional Infos Group: 16 bytes -/
structure LongOrderAdditionalInfosGroup where
  longClientId : Alpha 16
  deriving DecidableEq, Repr

namespace LongOrderAdditionalInfosGroup

def encode (message : LongOrderAdditionalInfosGroup) : List UInt8 :=
  Alpha.encode message.longClientId

def decode (bytes : List UInt8) : Option (LongOrderAdditionalInfosGroup × List UInt8) := do
  let (longClientId, bytes) ← Alpha.decode 16 bytes
  pure ({ longClientId }, bytes)

@[simp] theorem encode_length (message : LongOrderAdditionalInfosGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LongOrderAdditionalInfosGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderAdditionalInfosGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LongOrderAdditionalInfosGroup

/-- Long Order Additional Infos Groups -/
structure LongOrderAdditionalInfosGroups where
  blockLengthShort : BitVec 8
  longOrderAdditionalInfosGroup : Bounded 1 LongOrderAdditionalInfosGroup
  deriving DecidableEq, Repr

namespace LongOrderAdditionalInfosGroups

def encode (message : LongOrderAdditionalInfosGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderAdditionalInfosGroup.val.length)
    ++ (encodeMany LongOrderAdditionalInfosGroup.encode message.longOrderAdditionalInfosGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderAdditionalInfosGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderAdditionalInfosGroup_, bytes) ← decodeMany LongOrderAdditionalInfosGroup.decode numInGroup.toNat bytes
  if fits_longOrderAdditionalInfosGroup : longOrderAdditionalInfosGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderAdditionalInfosGroup := ⟨longOrderAdditionalInfosGroup_, fits_longOrderAdditionalInfosGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderAdditionalInfosGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderAdditionalInfosGroups) : (encode message).length ≤ 4082 := by
  have bound_longOrderAdditionalInfosGroup := message.longOrderAdditionalInfosGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderAdditionalInfosGroup.encode 16 LongOrderAdditionalInfosGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderAdditionalInfosGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderAdditionalInfosGroup.encode LongOrderAdditionalInfosGroup.decode LongOrderAdditionalInfosGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderAdditionalInfosGroup.length_lt]
  rfl

end LongOrderAdditionalInfosGroups

/-- Long Order Short Codes Details Non Modifiable Group: 3 bytes -/
structure LongOrderShortCodesDetailsNonModifiableGroup where
  originalShortCodeType : BitVec 8
  shortCodeRole : BitVec 8
  shortCodeRoleQualifier : BitVec 8
  deriving DecidableEq, Repr

namespace LongOrderShortCodesDetailsNonModifiableGroup

def encode (message : LongOrderShortCodesDetailsNonModifiableGroup) : List UInt8 :=
  encodeUInt 1 message.originalShortCodeType
    ++ (encodeUInt 1 message.shortCodeRole
    ++ (encodeUInt 1 message.shortCodeRoleQualifier))

def decode (bytes : List UInt8) : Option (LongOrderShortCodesDetailsNonModifiableGroup × List UInt8) := do
  let (originalShortCodeType, bytes) ← decodeUInt 1 bytes
  let (shortCodeRole, bytes) ← decodeUInt 1 bytes
  let (shortCodeRoleQualifier, bytes) ← decodeUInt 1 bytes
  pure ({ originalShortCodeType, shortCodeRole, shortCodeRoleQualifier }, bytes)

@[simp] theorem encode_length (message : LongOrderShortCodesDetailsNonModifiableGroup) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : LongOrderShortCodesDetailsNonModifiableGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderShortCodesDetailsNonModifiableGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LongOrderShortCodesDetailsNonModifiableGroup

/-- Long Order Short Codes Details Non Modifiable Groups -/
structure LongOrderShortCodesDetailsNonModifiableGroups where
  blockLengthShort : BitVec 8
  longOrderShortCodesDetailsNonModifiableGroup : Bounded 1 LongOrderShortCodesDetailsNonModifiableGroup
  deriving DecidableEq, Repr

namespace LongOrderShortCodesDetailsNonModifiableGroups

def encode (message : LongOrderShortCodesDetailsNonModifiableGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderShortCodesDetailsNonModifiableGroup.val.length)
    ++ (encodeMany LongOrderShortCodesDetailsNonModifiableGroup.encode message.longOrderShortCodesDetailsNonModifiableGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderShortCodesDetailsNonModifiableGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderShortCodesDetailsNonModifiableGroup_, bytes) ← decodeMany LongOrderShortCodesDetailsNonModifiableGroup.decode numInGroup.toNat bytes
  if fits_longOrderShortCodesDetailsNonModifiableGroup : longOrderShortCodesDetailsNonModifiableGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderShortCodesDetailsNonModifiableGroup := ⟨longOrderShortCodesDetailsNonModifiableGroup_, fits_longOrderShortCodesDetailsNonModifiableGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderShortCodesDetailsNonModifiableGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderShortCodesDetailsNonModifiableGroups) : (encode message).length ≤ 767 := by
  have bound_longOrderShortCodesDetailsNonModifiableGroup := message.longOrderShortCodesDetailsNonModifiableGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderShortCodesDetailsNonModifiableGroup.encode 3 LongOrderShortCodesDetailsNonModifiableGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderShortCodesDetailsNonModifiableGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderShortCodesDetailsNonModifiableGroup.encode LongOrderShortCodesDetailsNonModifiableGroup.decode LongOrderShortCodesDetailsNonModifiableGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderShortCodesDetailsNonModifiableGroup.length_lt]
  rfl

end LongOrderShortCodesDetailsNonModifiableGroups

/-- Long Order Short Codes Details Modifiable Group: 3 bytes -/
structure LongOrderShortCodesDetailsModifiableGroup where
  eventShortCodeType : BitVec 8
  shortCodeRole : BitVec 8
  shortCodeRoleQualifier : BitVec 8
  deriving DecidableEq, Repr

namespace LongOrderShortCodesDetailsModifiableGroup

def encode (message : LongOrderShortCodesDetailsModifiableGroup) : List UInt8 :=
  encodeUInt 1 message.eventShortCodeType
    ++ (encodeUInt 1 message.shortCodeRole
    ++ (encodeUInt 1 message.shortCodeRoleQualifier))

def decode (bytes : List UInt8) : Option (LongOrderShortCodesDetailsModifiableGroup × List UInt8) := do
  let (eventShortCodeType, bytes) ← decodeUInt 1 bytes
  let (shortCodeRole, bytes) ← decodeUInt 1 bytes
  let (shortCodeRoleQualifier, bytes) ← decodeUInt 1 bytes
  pure ({ eventShortCodeType, shortCodeRole, shortCodeRoleQualifier }, bytes)

@[simp] theorem encode_length (message : LongOrderShortCodesDetailsModifiableGroup) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : LongOrderShortCodesDetailsModifiableGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderShortCodesDetailsModifiableGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LongOrderShortCodesDetailsModifiableGroup

/-- Long Order Short Codes Details Modifiable Groups -/
structure LongOrderShortCodesDetailsModifiableGroups where
  blockLengthShort : BitVec 8
  longOrderShortCodesDetailsModifiableGroup : Bounded 1 LongOrderShortCodesDetailsModifiableGroup
  deriving DecidableEq, Repr

namespace LongOrderShortCodesDetailsModifiableGroups

def encode (message : LongOrderShortCodesDetailsModifiableGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderShortCodesDetailsModifiableGroup.val.length)
    ++ (encodeMany LongOrderShortCodesDetailsModifiableGroup.encode message.longOrderShortCodesDetailsModifiableGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderShortCodesDetailsModifiableGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderShortCodesDetailsModifiableGroup_, bytes) ← decodeMany LongOrderShortCodesDetailsModifiableGroup.decode numInGroup.toNat bytes
  if fits_longOrderShortCodesDetailsModifiableGroup : longOrderShortCodesDetailsModifiableGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderShortCodesDetailsModifiableGroup := ⟨longOrderShortCodesDetailsModifiableGroup_, fits_longOrderShortCodesDetailsModifiableGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderShortCodesDetailsModifiableGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderShortCodesDetailsModifiableGroups) : (encode message).length ≤ 767 := by
  have bound_longOrderShortCodesDetailsModifiableGroup := message.longOrderShortCodesDetailsModifiableGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderShortCodesDetailsModifiableGroup.encode 3 LongOrderShortCodesDetailsModifiableGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderShortCodesDetailsModifiableGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderShortCodesDetailsModifiableGroup.encode LongOrderShortCodesDetailsModifiableGroup.decode LongOrderShortCodesDetailsModifiableGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderShortCodesDetailsModifiableGroup.length_lt]
  rfl

end LongOrderShortCodesDetailsModifiableGroups

/-- Long Order Message -/
structure LongOrderMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  orderEventType : BitVec 8
  accountTypeInternal : BitVec 8
  ackPhase : BitVec 8
  ackQualifiers : BitVec 8
  ackType : BitVec 8
  bookInOptional : BitVec 64
  bookOutTimeOptional : BitVec 64
  clientOrderIdOptional : BitVec 64
  darkExecutionInstruction : BitVec 8
  emm : BitVec 8
  eventId : BitVec 64
  executionInstruction : BitVec 8
  firmId : Alpha 8
  indicativeAuctionPrice : BitVec 64
  indicativeAuctionVolume : BitVec 64
  oeSessionId : BitVec 64
  lpRoleOptional : BitVec 8
  miFidIndicators : BitVec 8
  oeginFromMemberOptional : BitVec 64
  oegoutTimeToMeOptional : BitVec 64
  orderId : BitVec 64
  orderPriority : BitVec 64
  orderPx : BitVec 64
  orderQty : BitVec 64
  orderSide : BitVec 8
  orderType : BitVec 8
  origClientOrderId : BitVec 64
  stpid : BitVec 16
  symbolIndex : BitVec 32
  timeInForce : BitVec 8
  displayedQty : BitVec 64
  crossOrderIndicator : BitVec 8
  counterpartFirmId : Alpha 8
  executionIdOptional : BitVec 32
  executionPhaseOptional : BitVec 8
  lastSharesOptional : BitVec 64
  lastTradedPxOptional : BitVec 64
  leavesQty : BitVec 64
  tradeQualifierOptional : BitVec 8
  tradeTime : BitVec 64
  tradeType : BitVec 8
  killReason : BitVec 16
  breachedCollarPrice : BitVec 64
  collarRejType : BitVec 8
  rejectedMessage : BitVec 8
  errorCodeOptional : BitVec 16
  stopQueuePriority : BitVec 64
  counterpartyReasonType : BitVec 8
  quoteIndicator : BitVec 8
  lisTransactionId : BitVec 32
  wholesaleTradeType : BitVec 8
  escbMembership : BitVec 8
  tradeUniqueIdentifier : Alpha 16
  orderTolerablePrice : BitVec 64
  orderSweepReason : BitVec 8
  longOrderFreeTextSectionGroups : LongOrderFreeTextSectionGroups
  longOrderOptionalFieldsGroups : LongOrderOptionalFieldsGroups
  longOrderClearingFieldsGroups : LongOrderClearingFieldsGroups
  longOrderNonModifiableOptFieldsGroups : LongOrderNonModifiableOptFieldsGroups
  longOrderNonModifiableShortCodesGroups : LongOrderNonModifiableShortCodesGroups
  longOrderModifiableShortCodesGroups : LongOrderModifiableShortCodesGroups
  longOrderCommercialFieldsGroups : LongOrderCommercialFieldsGroups
  longOrderModifiableCommercialInvestorFieldGroups : LongOrderModifiableCommercialInvestorFieldGroups
  longOrderNonModifiableCommercialInvestorFieldGroups : LongOrderNonModifiableCommercialInvestorFieldGroups
  longOrderExtendedClearingAccountGroups : LongOrderExtendedClearingAccountGroups
  longOrderStrategyFieldsGroups : LongOrderStrategyFieldsGroups
  longOrderOptionalFieldsDerivativesGroups : LongOrderOptionalFieldsDerivativesGroups
  longOrderAdditionalInfosGroups : LongOrderAdditionalInfosGroups
  longOrderShortCodesDetailsNonModifiableGroups : LongOrderShortCodesDetailsNonModifiableGroups
  longOrderShortCodesDetailsModifiableGroups : LongOrderShortCodesDetailsModifiableGroups
  deriving DecidableEq, Repr

namespace LongOrderMessage

def encode (message : LongOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUInt 1 message.orderEventType
    ++ (encodeUInt 1 message.accountTypeInternal
    ++ (encodeUInt 1 message.ackPhase
    ++ (encodeUIntLE 1 message.ackQualifiers
    ++ (encodeUInt 1 message.ackType
    ++ (encodeUIntLE 8 message.bookInOptional
    ++ (encodeUIntLE 8 message.bookOutTimeOptional
    ++ (encodeUIntLE 8 message.clientOrderIdOptional
    ++ (encodeUIntLE 1 message.darkExecutionInstruction
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUIntLE 1 message.executionInstruction
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.indicativeAuctionPrice
    ++ (encodeUIntLE 8 message.indicativeAuctionVolume
    ++ (encodeUIntLE 8 message.oeSessionId
    ++ (encodeUInt 1 message.lpRoleOptional
    ++ (encodeUIntLE 1 message.miFidIndicators
    ++ (encodeUIntLE 8 message.oeginFromMemberOptional
    ++ (encodeUIntLE 8 message.oegoutTimeToMeOptional
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.orderPriority
    ++ (encodeUIntLE 8 message.orderPx
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUInt 1 message.orderSide
    ++ (encodeUInt 1 message.orderType
    ++ (encodeUIntLE 8 message.origClientOrderId
    ++ (encodeUIntLE 2 message.stpid
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUIntLE 8 message.displayedQty
    ++ (encodeUInt 1 message.crossOrderIndicator
    ++ (Alpha.encode message.counterpartFirmId
    ++ (encodeUIntLE 4 message.executionIdOptional
    ++ (encodeUInt 1 message.executionPhaseOptional
    ++ (encodeUIntLE 8 message.lastSharesOptional
    ++ (encodeUIntLE 8 message.lastTradedPxOptional
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 1 message.tradeQualifierOptional
    ++ (encodeUIntLE 8 message.tradeTime
    ++ (encodeUInt 1 message.tradeType
    ++ (encodeUIntLE 2 message.killReason
    ++ (encodeUIntLE 8 message.breachedCollarPrice
    ++ (encodeUInt 1 message.collarRejType
    ++ (encodeUInt 1 message.rejectedMessage
    ++ (encodeUIntLE 2 message.errorCodeOptional
    ++ (encodeUIntLE 8 message.stopQueuePriority
    ++ (encodeUInt 1 message.counterpartyReasonType
    ++ (encodeUInt 1 message.quoteIndicator
    ++ (encodeUIntLE 4 message.lisTransactionId
    ++ (encodeUInt 1 message.wholesaleTradeType
    ++ (encodeUInt 1 message.escbMembership
    ++ (Alpha.encode message.tradeUniqueIdentifier
    ++ (encodeUIntLE 8 message.orderTolerablePrice
    ++ (encodeUInt 1 message.orderSweepReason
    ++ (LongOrderFreeTextSectionGroups.encode message.longOrderFreeTextSectionGroups
    ++ (LongOrderOptionalFieldsGroups.encode message.longOrderOptionalFieldsGroups
    ++ (LongOrderClearingFieldsGroups.encode message.longOrderClearingFieldsGroups
    ++ (LongOrderNonModifiableOptFieldsGroups.encode message.longOrderNonModifiableOptFieldsGroups
    ++ (LongOrderNonModifiableShortCodesGroups.encode message.longOrderNonModifiableShortCodesGroups
    ++ (LongOrderModifiableShortCodesGroups.encode message.longOrderModifiableShortCodesGroups
    ++ (LongOrderCommercialFieldsGroups.encode message.longOrderCommercialFieldsGroups
    ++ (LongOrderModifiableCommercialInvestorFieldGroups.encode message.longOrderModifiableCommercialInvestorFieldGroups
    ++ (LongOrderNonModifiableCommercialInvestorFieldGroups.encode message.longOrderNonModifiableCommercialInvestorFieldGroups
    ++ (LongOrderExtendedClearingAccountGroups.encode message.longOrderExtendedClearingAccountGroups
    ++ (LongOrderStrategyFieldsGroups.encode message.longOrderStrategyFieldsGroups
    ++ (LongOrderOptionalFieldsDerivativesGroups.encode message.longOrderOptionalFieldsDerivativesGroups
    ++ (LongOrderAdditionalInfosGroups.encode message.longOrderAdditionalInfosGroups
    ++ (LongOrderShortCodesDetailsNonModifiableGroups.encode message.longOrderShortCodesDetailsNonModifiableGroups
    ++ (LongOrderShortCodesDetailsModifiableGroups.encode message.longOrderShortCodesDetailsModifiableGroups))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (LongOrderMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (orderEventType, bytes) ← decodeUInt 1 bytes
  let (accountTypeInternal, bytes) ← decodeUInt 1 bytes
  let (ackPhase, bytes) ← decodeUInt 1 bytes
  let (ackQualifiers, bytes) ← decodeUIntLE 1 bytes
  let (ackType, bytes) ← decodeUInt 1 bytes
  let (bookInOptional, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (darkExecutionInstruction, bytes) ← decodeUIntLE 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (executionInstruction, bytes) ← decodeUIntLE 1 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (indicativeAuctionPrice, bytes) ← decodeUIntLE 8 bytes
  let (indicativeAuctionVolume, bytes) ← decodeUIntLE 8 bytes
  let (oeSessionId, bytes) ← decodeUIntLE 8 bytes
  let (lpRoleOptional, bytes) ← decodeUInt 1 bytes
  let (miFidIndicators, bytes) ← decodeUIntLE 1 bytes
  let (oeginFromMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegoutTimeToMeOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (orderPriority, bytes) ← decodeUIntLE 8 bytes
  let (orderPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (orderSide, bytes) ← decodeUInt 1 bytes
  let (orderType, bytes) ← decodeUInt 1 bytes
  let (origClientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (stpid, bytes) ← decodeUIntLE 2 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (displayedQty, bytes) ← decodeUIntLE 8 bytes
  let (crossOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (counterpartFirmId, bytes) ← Alpha.decode 8 bytes
  let (executionIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (executionPhaseOptional, bytes) ← decodeUInt 1 bytes
  let (lastSharesOptional, bytes) ← decodeUIntLE 8 bytes
  let (lastTradedPxOptional, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (tradeQualifierOptional, bytes) ← decodeUIntLE 1 bytes
  let (tradeTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeType, bytes) ← decodeUInt 1 bytes
  let (killReason, bytes) ← decodeUIntLE 2 bytes
  let (breachedCollarPrice, bytes) ← decodeUIntLE 8 bytes
  let (collarRejType, bytes) ← decodeUInt 1 bytes
  let (rejectedMessage, bytes) ← decodeUInt 1 bytes
  let (errorCodeOptional, bytes) ← decodeUIntLE 2 bytes
  let (stopQueuePriority, bytes) ← decodeUIntLE 8 bytes
  let (counterpartyReasonType, bytes) ← decodeUInt 1 bytes
  let (quoteIndicator, bytes) ← decodeUInt 1 bytes
  let (lisTransactionId, bytes) ← decodeUIntLE 4 bytes
  let (wholesaleTradeType, bytes) ← decodeUInt 1 bytes
  let (escbMembership, bytes) ← decodeUInt 1 bytes
  let (tradeUniqueIdentifier, bytes) ← Alpha.decode 16 bytes
  let (orderTolerablePrice, bytes) ← decodeUIntLE 8 bytes
  let (orderSweepReason, bytes) ← decodeUInt 1 bytes
  let (longOrderFreeTextSectionGroups, bytes) ← LongOrderFreeTextSectionGroups.decode bytes
  let (longOrderOptionalFieldsGroups, bytes) ← LongOrderOptionalFieldsGroups.decode bytes
  let (longOrderClearingFieldsGroups, bytes) ← LongOrderClearingFieldsGroups.decode bytes
  let (longOrderNonModifiableOptFieldsGroups, bytes) ← LongOrderNonModifiableOptFieldsGroups.decode bytes
  let (longOrderNonModifiableShortCodesGroups, bytes) ← LongOrderNonModifiableShortCodesGroups.decode bytes
  let (longOrderModifiableShortCodesGroups, bytes) ← LongOrderModifiableShortCodesGroups.decode bytes
  let (longOrderCommercialFieldsGroups, bytes) ← LongOrderCommercialFieldsGroups.decode bytes
  let (longOrderModifiableCommercialInvestorFieldGroups, bytes) ← LongOrderModifiableCommercialInvestorFieldGroups.decode bytes
  let (longOrderNonModifiableCommercialInvestorFieldGroups, bytes) ← LongOrderNonModifiableCommercialInvestorFieldGroups.decode bytes
  let (longOrderExtendedClearingAccountGroups, bytes) ← LongOrderExtendedClearingAccountGroups.decode bytes
  let (longOrderStrategyFieldsGroups, bytes) ← LongOrderStrategyFieldsGroups.decode bytes
  let (longOrderOptionalFieldsDerivativesGroups, bytes) ← LongOrderOptionalFieldsDerivativesGroups.decode bytes
  let (longOrderAdditionalInfosGroups, bytes) ← LongOrderAdditionalInfosGroups.decode bytes
  let (longOrderShortCodesDetailsNonModifiableGroups, bytes) ← LongOrderShortCodesDetailsNonModifiableGroups.decode bytes
  let (longOrderShortCodesDetailsModifiableGroups, bytes) ← LongOrderShortCodesDetailsModifiableGroups.decode bytes
  pure ({ msgSeqNum, produceTime, consumeTime, orderEventType, accountTypeInternal, ackPhase, ackQualifiers, ackType, bookInOptional, bookOutTimeOptional, clientOrderIdOptional, darkExecutionInstruction, emm, eventId, executionInstruction, firmId, indicativeAuctionPrice, indicativeAuctionVolume, oeSessionId, lpRoleOptional, miFidIndicators, oeginFromMemberOptional, oegoutTimeToMeOptional, orderId, orderPriority, orderPx, orderQty, orderSide, orderType, origClientOrderId, stpid, symbolIndex, timeInForce, displayedQty, crossOrderIndicator, counterpartFirmId, executionIdOptional, executionPhaseOptional, lastSharesOptional, lastTradedPxOptional, leavesQty, tradeQualifierOptional, tradeTime, tradeType, killReason, breachedCollarPrice, collarRejType, rejectedMessage, errorCodeOptional, stopQueuePriority, counterpartyReasonType, quoteIndicator, lisTransactionId, wholesaleTradeType, escbMembership, tradeUniqueIdentifier, orderTolerablePrice, orderSweepReason, longOrderFreeTextSectionGroups, longOrderOptionalFieldsGroups, longOrderClearingFieldsGroups, longOrderNonModifiableOptFieldsGroups, longOrderNonModifiableShortCodesGroups, longOrderModifiableShortCodesGroups, longOrderCommercialFieldsGroups, longOrderModifiableCommercialInvestorFieldGroups, longOrderNonModifiableCommercialInvestorFieldGroups, longOrderExtendedClearingAccountGroups, longOrderStrategyFieldsGroups, longOrderOptionalFieldsDerivativesGroups, longOrderAdditionalInfosGroups, longOrderShortCodesDetailsNonModifiableGroups, longOrderShortCodesDetailsModifiableGroups }, bytes)

theorem encode_length_pos (message : LongOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderMessage) : (encode message).length ≤ 73740 := by
  have bound_longOrderFreeTextSectionGroups := LongOrderFreeTextSectionGroups.encode_length_le message.longOrderFreeTextSectionGroups
  have bound_longOrderOptionalFieldsGroups := LongOrderOptionalFieldsGroups.encode_length_le message.longOrderOptionalFieldsGroups
  have bound_longOrderClearingFieldsGroups := LongOrderClearingFieldsGroups.encode_length_le message.longOrderClearingFieldsGroups
  have bound_longOrderNonModifiableOptFieldsGroups := LongOrderNonModifiableOptFieldsGroups.encode_length_le message.longOrderNonModifiableOptFieldsGroups
  have bound_longOrderNonModifiableShortCodesGroups := LongOrderNonModifiableShortCodesGroups.encode_length_le message.longOrderNonModifiableShortCodesGroups
  have bound_longOrderModifiableShortCodesGroups := LongOrderModifiableShortCodesGroups.encode_length_le message.longOrderModifiableShortCodesGroups
  have bound_longOrderCommercialFieldsGroups := LongOrderCommercialFieldsGroups.encode_length_le message.longOrderCommercialFieldsGroups
  have bound_longOrderModifiableCommercialInvestorFieldGroups := LongOrderModifiableCommercialInvestorFieldGroups.encode_length_le message.longOrderModifiableCommercialInvestorFieldGroups
  have bound_longOrderNonModifiableCommercialInvestorFieldGroups := LongOrderNonModifiableCommercialInvestorFieldGroups.encode_length_le message.longOrderNonModifiableCommercialInvestorFieldGroups
  have bound_longOrderExtendedClearingAccountGroups := LongOrderExtendedClearingAccountGroups.encode_length_le message.longOrderExtendedClearingAccountGroups
  have bound_longOrderStrategyFieldsGroups := LongOrderStrategyFieldsGroups.encode_length_le message.longOrderStrategyFieldsGroups
  have bound_longOrderOptionalFieldsDerivativesGroups := LongOrderOptionalFieldsDerivativesGroups.encode_length_le message.longOrderOptionalFieldsDerivativesGroups
  have bound_longOrderAdditionalInfosGroups := LongOrderAdditionalInfosGroups.encode_length_le message.longOrderAdditionalInfosGroups
  have bound_longOrderShortCodesDetailsNonModifiableGroups := LongOrderShortCodesDetailsNonModifiableGroups.encode_length_le message.longOrderShortCodesDetailsNonModifiableGroups
  have bound_longOrderShortCodesDetailsModifiableGroups := LongOrderShortCodesDetailsModifiableGroups.encode_length_le message.longOrderShortCodesDetailsModifiableGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : LongOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderFreeTextSectionGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderOptionalFieldsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderClearingFieldsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderNonModifiableOptFieldsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderNonModifiableShortCodesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderModifiableShortCodesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderCommercialFieldsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderModifiableCommercialInvestorFieldGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderNonModifiableCommercialInvestorFieldGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderExtendedClearingAccountGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderStrategyFieldsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderOptionalFieldsDerivativesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderAdditionalInfosGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongOrderShortCodesDetailsNonModifiableGroups.decode_encode, some_bind]
  dsimp only
  rw [LongOrderShortCodesDetailsModifiableGroups.decode_encode, some_bind]
  rfl

end LongOrderMessage

/-- D C Short Order Reject Message Modifiable Short Codes Group: 8 bytes -/
structure DCShortOrderRejectMessageModifiableShortCodesGroup where
  eventClientIdShortCode : BitVec 32
  eventExecWFirmShortCode : BitVec 32
  deriving DecidableEq, Repr

namespace DCShortOrderRejectMessageModifiableShortCodesGroup

def encode (message : DCShortOrderRejectMessageModifiableShortCodesGroup) : List UInt8 :=
  encodeUIntLE 4 message.eventClientIdShortCode
    ++ (encodeUIntLE 4 message.eventExecWFirmShortCode)

def decode (bytes : List UInt8) : Option (DCShortOrderRejectMessageModifiableShortCodesGroup × List UInt8) := do
  let (eventClientIdShortCode, bytes) ← decodeUIntLE 4 bytes
  let (eventExecWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  pure ({ eventClientIdShortCode, eventExecWFirmShortCode }, bytes)

@[simp] theorem encode_length (message : DCShortOrderRejectMessageModifiableShortCodesGroup) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DCShortOrderRejectMessageModifiableShortCodesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCShortOrderRejectMessageModifiableShortCodesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DCShortOrderRejectMessageModifiableShortCodesGroup

/-- D C Short Order Reject Message Modifiable Short Codes Groups -/
structure DCShortOrderRejectMessageModifiableShortCodesGroups where
  blockLengthShort : BitVec 8
  dCShortOrderRejectMessageModifiableShortCodesGroup : Bounded 1 DCShortOrderRejectMessageModifiableShortCodesGroup
  deriving DecidableEq, Repr

namespace DCShortOrderRejectMessageModifiableShortCodesGroups

def encode (message : DCShortOrderRejectMessageModifiableShortCodesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCShortOrderRejectMessageModifiableShortCodesGroup.val.length)
    ++ (encodeMany DCShortOrderRejectMessageModifiableShortCodesGroup.encode message.dCShortOrderRejectMessageModifiableShortCodesGroup.val))

def decode (bytes : List UInt8) : Option (DCShortOrderRejectMessageModifiableShortCodesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCShortOrderRejectMessageModifiableShortCodesGroup_, bytes) ← decodeMany DCShortOrderRejectMessageModifiableShortCodesGroup.decode numInGroup.toNat bytes
  if fits_dCShortOrderRejectMessageModifiableShortCodesGroup : dCShortOrderRejectMessageModifiableShortCodesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCShortOrderRejectMessageModifiableShortCodesGroup := ⟨dCShortOrderRejectMessageModifiableShortCodesGroup_, fits_dCShortOrderRejectMessageModifiableShortCodesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCShortOrderRejectMessageModifiableShortCodesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCShortOrderRejectMessageModifiableShortCodesGroups) : (encode message).length ≤ 2042 := by
  have bound_dCShortOrderRejectMessageModifiableShortCodesGroup := message.dCShortOrderRejectMessageModifiableShortCodesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCShortOrderRejectMessageModifiableShortCodesGroup.encode 8 DCShortOrderRejectMessageModifiableShortCodesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCShortOrderRejectMessageModifiableShortCodesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCShortOrderRejectMessageModifiableShortCodesGroup.encode DCShortOrderRejectMessageModifiableShortCodesGroup.decode DCShortOrderRejectMessageModifiableShortCodesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCShortOrderRejectMessageModifiableShortCodesGroup.length_lt]
  rfl

end DCShortOrderRejectMessageModifiableShortCodesGroups

/-- D C Short Order Reject Message Short Codes Details Modifiable Group: 3 bytes -/
structure DCShortOrderRejectMessageShortCodesDetailsModifiableGroup where
  eventShortCodeType : BitVec 8
  shortCodeRole : BitVec 8
  shortCodeRoleQualifier : BitVec 8
  deriving DecidableEq, Repr

namespace DCShortOrderRejectMessageShortCodesDetailsModifiableGroup

def encode (message : DCShortOrderRejectMessageShortCodesDetailsModifiableGroup) : List UInt8 :=
  encodeUInt 1 message.eventShortCodeType
    ++ (encodeUInt 1 message.shortCodeRole
    ++ (encodeUInt 1 message.shortCodeRoleQualifier))

def decode (bytes : List UInt8) : Option (DCShortOrderRejectMessageShortCodesDetailsModifiableGroup × List UInt8) := do
  let (eventShortCodeType, bytes) ← decodeUInt 1 bytes
  let (shortCodeRole, bytes) ← decodeUInt 1 bytes
  let (shortCodeRoleQualifier, bytes) ← decodeUInt 1 bytes
  pure ({ eventShortCodeType, shortCodeRole, shortCodeRoleQualifier }, bytes)

@[simp] theorem encode_length (message : DCShortOrderRejectMessageShortCodesDetailsModifiableGroup) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : DCShortOrderRejectMessageShortCodesDetailsModifiableGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCShortOrderRejectMessageShortCodesDetailsModifiableGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DCShortOrderRejectMessageShortCodesDetailsModifiableGroup

/-- D C Short Order Reject Message Short Codes Details Modifiable Groups -/
structure DCShortOrderRejectMessageShortCodesDetailsModifiableGroups where
  blockLengthShort : BitVec 8
  dCShortOrderRejectMessageShortCodesDetailsModifiableGroup : Bounded 1 DCShortOrderRejectMessageShortCodesDetailsModifiableGroup
  deriving DecidableEq, Repr

namespace DCShortOrderRejectMessageShortCodesDetailsModifiableGroups

def encode (message : DCShortOrderRejectMessageShortCodesDetailsModifiableGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCShortOrderRejectMessageShortCodesDetailsModifiableGroup.val.length)
    ++ (encodeMany DCShortOrderRejectMessageShortCodesDetailsModifiableGroup.encode message.dCShortOrderRejectMessageShortCodesDetailsModifiableGroup.val))

def decode (bytes : List UInt8) : Option (DCShortOrderRejectMessageShortCodesDetailsModifiableGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCShortOrderRejectMessageShortCodesDetailsModifiableGroup_, bytes) ← decodeMany DCShortOrderRejectMessageShortCodesDetailsModifiableGroup.decode numInGroup.toNat bytes
  if fits_dCShortOrderRejectMessageShortCodesDetailsModifiableGroup : dCShortOrderRejectMessageShortCodesDetailsModifiableGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCShortOrderRejectMessageShortCodesDetailsModifiableGroup := ⟨dCShortOrderRejectMessageShortCodesDetailsModifiableGroup_, fits_dCShortOrderRejectMessageShortCodesDetailsModifiableGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCShortOrderRejectMessageShortCodesDetailsModifiableGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCShortOrderRejectMessageShortCodesDetailsModifiableGroups) : (encode message).length ≤ 767 := by
  have bound_dCShortOrderRejectMessageShortCodesDetailsModifiableGroup := message.dCShortOrderRejectMessageShortCodesDetailsModifiableGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCShortOrderRejectMessageShortCodesDetailsModifiableGroup.encode 3 DCShortOrderRejectMessageShortCodesDetailsModifiableGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCShortOrderRejectMessageShortCodesDetailsModifiableGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCShortOrderRejectMessageShortCodesDetailsModifiableGroup.encode DCShortOrderRejectMessageShortCodesDetailsModifiableGroup.decode DCShortOrderRejectMessageShortCodesDetailsModifiableGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCShortOrderRejectMessageShortCodesDetailsModifiableGroup.length_lt]
  rfl

end DCShortOrderRejectMessageShortCodesDetailsModifiableGroups

/-- Dc Short Order Reject Message -/
structure DcShortOrderRejectMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  orderEventType : BitVec 8
  bookIn : BitVec 64
  bookOutTime : BitVec 64
  clientOrderId : BitVec 64
  emm : BitVec 8
  eventId : BitVec 64
  firmId : Alpha 8
  oeginFromMemberOptional : BitVec 64
  oegoutTimeToMe : BitVec 64
  orderId : BitVec 64
  symbolIndex : BitVec 32
  breachedCollarPrice : BitVec 64
  collarRejType : BitVec 8
  rejectedMessage : BitVec 8
  errorCode : BitVec 16
  miFidIndicatorsOptional : BitVec 8
  oeSessionIdOptional : BitVec 64
  orderSideOptional : BitVec 8
  timeInForceOptional : BitVec 8
  dCShortOrderRejectMessageModifiableShortCodesGroups : DCShortOrderRejectMessageModifiableShortCodesGroups
  dCShortOrderRejectMessageShortCodesDetailsModifiableGroups : DCShortOrderRejectMessageShortCodesDetailsModifiableGroups
  deriving DecidableEq, Repr

namespace DcShortOrderRejectMessage

def encode (message : DcShortOrderRejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUInt 1 message.orderEventType
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTime
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventId
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.oeginFromMemberOptional
    ++ (encodeUIntLE 8 message.oegoutTimeToMe
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.breachedCollarPrice
    ++ (encodeUInt 1 message.collarRejType
    ++ (encodeUInt 1 message.rejectedMessage
    ++ (encodeUIntLE 2 message.errorCode
    ++ (encodeUIntLE 1 message.miFidIndicatorsOptional
    ++ (encodeUIntLE 8 message.oeSessionIdOptional
    ++ (encodeUInt 1 message.orderSideOptional
    ++ (encodeUInt 1 message.timeInForceOptional
    ++ (DCShortOrderRejectMessageModifiableShortCodesGroups.encode message.dCShortOrderRejectMessageModifiableShortCodesGroups
    ++ (DCShortOrderRejectMessageShortCodesDetailsModifiableGroups.encode message.dCShortOrderRejectMessageShortCodesDetailsModifiableGroups)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (DcShortOrderRejectMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (orderEventType, bytes) ← decodeUInt 1 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTime, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (oeginFromMemberOptional, bytes) ← decodeUIntLE 8 bytes
  let (oegoutTimeToMe, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (breachedCollarPrice, bytes) ← decodeUIntLE 8 bytes
  let (collarRejType, bytes) ← decodeUInt 1 bytes
  let (rejectedMessage, bytes) ← decodeUInt 1 bytes
  let (errorCode, bytes) ← decodeUIntLE 2 bytes
  let (miFidIndicatorsOptional, bytes) ← decodeUIntLE 1 bytes
  let (oeSessionIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderSideOptional, bytes) ← decodeUInt 1 bytes
  let (timeInForceOptional, bytes) ← decodeUInt 1 bytes
  let (dCShortOrderRejectMessageModifiableShortCodesGroups, bytes) ← DCShortOrderRejectMessageModifiableShortCodesGroups.decode bytes
  let (dCShortOrderRejectMessageShortCodesDetailsModifiableGroups, bytes) ← DCShortOrderRejectMessageShortCodesDetailsModifiableGroups.decode bytes
  pure ({ msgSeqNum, produceTime, consumeTime, orderEventType, bookIn, bookOutTime, clientOrderId, emm, eventId, firmId, oeginFromMemberOptional, oegoutTimeToMe, orderId, symbolIndex, breachedCollarPrice, collarRejType, rejectedMessage, errorCode, miFidIndicatorsOptional, oeSessionIdOptional, orderSideOptional, timeInForceOptional, dCShortOrderRejectMessageModifiableShortCodesGroups, dCShortOrderRejectMessageShortCodesDetailsModifiableGroups }, bytes)

theorem encode_length_pos (message : DcShortOrderRejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DcShortOrderRejectMessage) : (encode message).length ≤ 2922 := by
  have bound_dCShortOrderRejectMessageModifiableShortCodesGroups := DCShortOrderRejectMessageModifiableShortCodesGroups.encode_length_le message.dCShortOrderRejectMessageModifiableShortCodesGroups
  have bound_dCShortOrderRejectMessageShortCodesDetailsModifiableGroups := DCShortOrderRejectMessageShortCodesDetailsModifiableGroups.encode_length_le message.dCShortOrderRejectMessageShortCodesDetailsModifiableGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : DcShortOrderRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, DCShortOrderRejectMessageModifiableShortCodesGroups.decode_encode, some_bind]
  dsimp only
  rw [DCShortOrderRejectMessageShortCodesDetailsModifiableGroups.decode_encode, some_bind]
  rfl

end DcShortOrderRejectMessage

/-- Dc Short Trade Cancellation Message: 77 bytes -/
structure DcShortTradeCancellationMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  executionId : BitVec 32
  emm : BitVec 8
  eventId : BitVec 64
  symbolIndex : BitVec 32
  bookIn : BitVec 64
  lastTradedPx : BitVec 64
  lastShares : BitVec 64
  tradeUniqueIdentifier : Alpha 16
  deriving DecidableEq, Repr

namespace DcShortTradeCancellationMessage

def encode (message : DcShortTradeCancellationMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 4 message.executionId
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.lastTradedPx
    ++ (encodeUIntLE 8 message.lastShares
    ++ (Alpha.encode message.tradeUniqueIdentifier))))))))))

def decode (bytes : List UInt8) : Option (DcShortTradeCancellationMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (executionId, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (lastTradedPx, bytes) ← decodeUIntLE 8 bytes
  let (lastShares, bytes) ← decodeUIntLE 8 bytes
  let (tradeUniqueIdentifier, bytes) ← Alpha.decode 16 bytes
  pure ({ msgSeqNum, produceTime, consumeTime, executionId, emm, eventId, symbolIndex, bookIn, lastTradedPx, lastShares, tradeUniqueIdentifier }, bytes)

@[simp] theorem encode_length (message : DcShortTradeCancellationMessage) : (encode message).length = 77 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DcShortTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcShortTradeCancellationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end DcShortTradeCancellationMessage

/-- D C Static Collars Message Static Collarsrep Group: 9 bytes -/
structure DCStaticCollarsMessageStaticCollarsrepGroup where
  updateType : BitVec 8
  price : BitVec 64
  deriving DecidableEq, Repr

namespace DCStaticCollarsMessageStaticCollarsrepGroup

def encode (message : DCStaticCollarsMessageStaticCollarsrepGroup) : List UInt8 :=
  encodeUInt 1 message.updateType
    ++ (encodeUIntLE 8 message.price)

def decode (bytes : List UInt8) : Option (DCStaticCollarsMessageStaticCollarsrepGroup × List UInt8) := do
  let (updateType, bytes) ← decodeUInt 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ updateType, price }, bytes)

@[simp] theorem encode_length (message : DCStaticCollarsMessageStaticCollarsrepGroup) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : DCStaticCollarsMessageStaticCollarsrepGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCStaticCollarsMessageStaticCollarsrepGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DCStaticCollarsMessageStaticCollarsrepGroup

/-- D C Static Collars Message Static Collarsrep Groups -/
structure DCStaticCollarsMessageStaticCollarsrepGroups where
  blockLengthShort : BitVec 8
  dCStaticCollarsMessageStaticCollarsrepGroup : Bounded 1 DCStaticCollarsMessageStaticCollarsrepGroup
  deriving DecidableEq, Repr

namespace DCStaticCollarsMessageStaticCollarsrepGroups

def encode (message : DCStaticCollarsMessageStaticCollarsrepGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCStaticCollarsMessageStaticCollarsrepGroup.val.length)
    ++ (encodeMany DCStaticCollarsMessageStaticCollarsrepGroup.encode message.dCStaticCollarsMessageStaticCollarsrepGroup.val))

def decode (bytes : List UInt8) : Option (DCStaticCollarsMessageStaticCollarsrepGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCStaticCollarsMessageStaticCollarsrepGroup_, bytes) ← decodeMany DCStaticCollarsMessageStaticCollarsrepGroup.decode numInGroup.toNat bytes
  if fits_dCStaticCollarsMessageStaticCollarsrepGroup : dCStaticCollarsMessageStaticCollarsrepGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCStaticCollarsMessageStaticCollarsrepGroup := ⟨dCStaticCollarsMessageStaticCollarsrepGroup_, fits_dCStaticCollarsMessageStaticCollarsrepGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCStaticCollarsMessageStaticCollarsrepGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCStaticCollarsMessageStaticCollarsrepGroups) : (encode message).length ≤ 2297 := by
  have bound_dCStaticCollarsMessageStaticCollarsrepGroup := message.dCStaticCollarsMessageStaticCollarsrepGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCStaticCollarsMessageStaticCollarsrepGroup.encode 9 DCStaticCollarsMessageStaticCollarsrepGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCStaticCollarsMessageStaticCollarsrepGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCStaticCollarsMessageStaticCollarsrepGroup.encode DCStaticCollarsMessageStaticCollarsrepGroup.decode DCStaticCollarsMessageStaticCollarsrepGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCStaticCollarsMessageStaticCollarsrepGroup.length_lt]
  rfl

end DCStaticCollarsMessageStaticCollarsrepGroups

/-- Dc Static Collars Message -/
structure DcStaticCollarsMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  dCStaticCollarsMessageStaticCollarsrepGroups : DCStaticCollarsMessageStaticCollarsrepGroups
  deriving DecidableEq, Repr

namespace DcStaticCollarsMessage

def encode (message : DcStaticCollarsMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (DCStaticCollarsMessageStaticCollarsrepGroups.encode message.dCStaticCollarsMessageStaticCollarsrepGroups)))))

def decode (bytes : List UInt8) : Option (DcStaticCollarsMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (dCStaticCollarsMessageStaticCollarsrepGroups, bytes) ← DCStaticCollarsMessageStaticCollarsrepGroups.decode bytes
  pure ({ msgSeqNum, produceTime, consumeTime, symbolIndex, emm, dCStaticCollarsMessageStaticCollarsrepGroups }, bytes)

theorem encode_length_pos (message : DcStaticCollarsMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DcStaticCollarsMessage) : (encode message).length ≤ 2322 := by
  have bound_dCStaticCollarsMessageStaticCollarsrepGroups := DCStaticCollarsMessageStaticCollarsrepGroups.encode_length_le message.dCStaticCollarsMessageStaticCollarsrepGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : DcStaticCollarsMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [DCStaticCollarsMessageStaticCollarsrepGroups.decode_encode, some_bind]
  rfl

end DcStaticCollarsMessage

/-- Trade Bust Notification Short Codes Details Non Modifiable Group: 3 bytes -/
structure TradeBustNotificationShortCodesDetailsNonModifiableGroup where
  originalShortCodeType : BitVec 8
  shortCodeRole : BitVec 8
  shortCodeRoleQualifier : BitVec 8
  deriving DecidableEq, Repr

namespace TradeBustNotificationShortCodesDetailsNonModifiableGroup

def encode (message : TradeBustNotificationShortCodesDetailsNonModifiableGroup) : List UInt8 :=
  encodeUInt 1 message.originalShortCodeType
    ++ (encodeUInt 1 message.shortCodeRole
    ++ (encodeUInt 1 message.shortCodeRoleQualifier))

def decode (bytes : List UInt8) : Option (TradeBustNotificationShortCodesDetailsNonModifiableGroup × List UInt8) := do
  let (originalShortCodeType, bytes) ← decodeUInt 1 bytes
  let (shortCodeRole, bytes) ← decodeUInt 1 bytes
  let (shortCodeRoleQualifier, bytes) ← decodeUInt 1 bytes
  pure ({ originalShortCodeType, shortCodeRole, shortCodeRoleQualifier }, bytes)

@[simp] theorem encode_length (message : TradeBustNotificationShortCodesDetailsNonModifiableGroup) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TradeBustNotificationShortCodesDetailsNonModifiableGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustNotificationShortCodesDetailsNonModifiableGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeBustNotificationShortCodesDetailsNonModifiableGroup

/-- Trade Bust Notification Short Codes Details Non Modifiable Groups -/
structure TradeBustNotificationShortCodesDetailsNonModifiableGroups where
  blockLengthShort : BitVec 8
  tradeBustNotificationShortCodesDetailsNonModifiableGroup : Bounded 1 TradeBustNotificationShortCodesDetailsNonModifiableGroup
  deriving DecidableEq, Repr

namespace TradeBustNotificationShortCodesDetailsNonModifiableGroups

def encode (message : TradeBustNotificationShortCodesDetailsNonModifiableGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeBustNotificationShortCodesDetailsNonModifiableGroup.val.length)
    ++ (encodeMany TradeBustNotificationShortCodesDetailsNonModifiableGroup.encode message.tradeBustNotificationShortCodesDetailsNonModifiableGroup.val))

def decode (bytes : List UInt8) : Option (TradeBustNotificationShortCodesDetailsNonModifiableGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (tradeBustNotificationShortCodesDetailsNonModifiableGroup_, bytes) ← decodeMany TradeBustNotificationShortCodesDetailsNonModifiableGroup.decode numInGroup.toNat bytes
  if fits_tradeBustNotificationShortCodesDetailsNonModifiableGroup : tradeBustNotificationShortCodesDetailsNonModifiableGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, tradeBustNotificationShortCodesDetailsNonModifiableGroup := ⟨tradeBustNotificationShortCodesDetailsNonModifiableGroup_, fits_tradeBustNotificationShortCodesDetailsNonModifiableGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeBustNotificationShortCodesDetailsNonModifiableGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBustNotificationShortCodesDetailsNonModifiableGroups) : (encode message).length ≤ 767 := by
  have bound_tradeBustNotificationShortCodesDetailsNonModifiableGroup := message.tradeBustNotificationShortCodesDetailsNonModifiableGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const TradeBustNotificationShortCodesDetailsNonModifiableGroup.encode 3 TradeBustNotificationShortCodesDetailsNonModifiableGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeBustNotificationShortCodesDetailsNonModifiableGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 TradeBustNotificationShortCodesDetailsNonModifiableGroup.encode TradeBustNotificationShortCodesDetailsNonModifiableGroup.decode TradeBustNotificationShortCodesDetailsNonModifiableGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tradeBustNotificationShortCodesDetailsNonModifiableGroup.length_lt]
  rfl

end TradeBustNotificationShortCodesDetailsNonModifiableGroups

/-- Trade Bust Notification Short Codes Details Modifiable Group: 3 bytes -/
structure TradeBustNotificationShortCodesDetailsModifiableGroup where
  eventShortCodeType : BitVec 8
  shortCodeRole : BitVec 8
  shortCodeRoleQualifier : BitVec 8
  deriving DecidableEq, Repr

namespace TradeBustNotificationShortCodesDetailsModifiableGroup

def encode (message : TradeBustNotificationShortCodesDetailsModifiableGroup) : List UInt8 :=
  encodeUInt 1 message.eventShortCodeType
    ++ (encodeUInt 1 message.shortCodeRole
    ++ (encodeUInt 1 message.shortCodeRoleQualifier))

def decode (bytes : List UInt8) : Option (TradeBustNotificationShortCodesDetailsModifiableGroup × List UInt8) := do
  let (eventShortCodeType, bytes) ← decodeUInt 1 bytes
  let (shortCodeRole, bytes) ← decodeUInt 1 bytes
  let (shortCodeRoleQualifier, bytes) ← decodeUInt 1 bytes
  pure ({ eventShortCodeType, shortCodeRole, shortCodeRoleQualifier }, bytes)

@[simp] theorem encode_length (message : TradeBustNotificationShortCodesDetailsModifiableGroup) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TradeBustNotificationShortCodesDetailsModifiableGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustNotificationShortCodesDetailsModifiableGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeBustNotificationShortCodesDetailsModifiableGroup

/-- Trade Bust Notification Short Codes Details Modifiable Groups -/
structure TradeBustNotificationShortCodesDetailsModifiableGroups where
  blockLengthShort : BitVec 8
  tradeBustNotificationShortCodesDetailsModifiableGroup : Bounded 1 TradeBustNotificationShortCodesDetailsModifiableGroup
  deriving DecidableEq, Repr

namespace TradeBustNotificationShortCodesDetailsModifiableGroups

def encode (message : TradeBustNotificationShortCodesDetailsModifiableGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeBustNotificationShortCodesDetailsModifiableGroup.val.length)
    ++ (encodeMany TradeBustNotificationShortCodesDetailsModifiableGroup.encode message.tradeBustNotificationShortCodesDetailsModifiableGroup.val))

def decode (bytes : List UInt8) : Option (TradeBustNotificationShortCodesDetailsModifiableGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (tradeBustNotificationShortCodesDetailsModifiableGroup_, bytes) ← decodeMany TradeBustNotificationShortCodesDetailsModifiableGroup.decode numInGroup.toNat bytes
  if fits_tradeBustNotificationShortCodesDetailsModifiableGroup : tradeBustNotificationShortCodesDetailsModifiableGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, tradeBustNotificationShortCodesDetailsModifiableGroup := ⟨tradeBustNotificationShortCodesDetailsModifiableGroup_, fits_tradeBustNotificationShortCodesDetailsModifiableGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeBustNotificationShortCodesDetailsModifiableGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBustNotificationShortCodesDetailsModifiableGroups) : (encode message).length ≤ 767 := by
  have bound_tradeBustNotificationShortCodesDetailsModifiableGroup := message.tradeBustNotificationShortCodesDetailsModifiableGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const TradeBustNotificationShortCodesDetailsModifiableGroup.encode 3 TradeBustNotificationShortCodesDetailsModifiableGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeBustNotificationShortCodesDetailsModifiableGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 TradeBustNotificationShortCodesDetailsModifiableGroup.encode TradeBustNotificationShortCodesDetailsModifiableGroup.decode TradeBustNotificationShortCodesDetailsModifiableGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tradeBustNotificationShortCodesDetailsModifiableGroup.length_lt]
  rfl

end TradeBustNotificationShortCodesDetailsModifiableGroups

/-- Trade Bust Notification Message -/
structure TradeBustNotificationMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  firmId : Alpha 8
  oeSessionId : BitVec 64
  orderSide : BitVec 8
  bookOutTime : BitVec 64
  bookInTime : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  executionId : BitVec 32
  lastShares : BitVec 64
  lastTradedPx : BitVec 64
  orderId : BitVec 64
  miFidIndicators : BitVec 8
  clearingFirmId : Alpha 8
  tradingCapacity : BitVec 8
  oeginFromMember : BitVec 64
  executionPhase : BitVec 8
  tradeQualifier : BitVec 8
  counterpartFirmId : Alpha 8
  orderType : BitVec 8
  timeInForceOptional : BitVec 8
  clearingInstructionOptional : BitVec 16
  technicalOrigin : BitVec 8
  freeText : Alpha 18
  accountNumber : Alpha 12
  accountType : BitVec 8
  lpRoleOptional : BitVec 8
  openClose : BitVec 16
  originalInvestDecisWFirmShortCode : BitVec 32
  originalNonExecBrokerShortCode : BitVec 32
  eventClientIdShortCode : BitVec 32
  eventExecWFirmShortCode : BitVec 32
  originalClientIdShortCode : BitVec 32
  originalExecWFirmShortCode : BitVec 32
  clearingAccount : Alpha 16
  lisTransactionId : BitVec 32
  parentExecId : BitVec 32
  parentSymbolIndex : BitVec 32
  tradeUniqueIdentifier : Alpha 16
  parentTradeUniqueIdentifier : Alpha 16
  tradeBustNotificationShortCodesDetailsNonModifiableGroups : TradeBustNotificationShortCodesDetailsNonModifiableGroups
  tradeBustNotificationShortCodesDetailsModifiableGroups : TradeBustNotificationShortCodesDetailsModifiableGroups
  deriving DecidableEq, Repr

namespace TradeBustNotificationMessage

def encode (message : TradeBustNotificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.oeSessionId
    ++ (encodeUInt 1 message.orderSide
    ++ (encodeUIntLE 8 message.bookOutTime
    ++ (encodeUIntLE 8 message.bookInTime
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 4 message.executionId
    ++ (encodeUIntLE 8 message.lastShares
    ++ (encodeUIntLE 8 message.lastTradedPx
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 1 message.miFidIndicators
    ++ (Alpha.encode message.clearingFirmId
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUIntLE 8 message.oeginFromMember
    ++ (encodeUInt 1 message.executionPhase
    ++ (encodeUIntLE 1 message.tradeQualifier
    ++ (Alpha.encode message.counterpartFirmId
    ++ (encodeUInt 1 message.orderType
    ++ (encodeUInt 1 message.timeInForceOptional
    ++ (encodeUIntLE 2 message.clearingInstructionOptional
    ++ (encodeUInt 1 message.technicalOrigin
    ++ (Alpha.encode message.freeText
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.lpRoleOptional
    ++ (encodeUIntLE 2 message.openClose
    ++ (encodeUIntLE 4 message.originalInvestDecisWFirmShortCode
    ++ (encodeUIntLE 4 message.originalNonExecBrokerShortCode
    ++ (encodeUIntLE 4 message.eventClientIdShortCode
    ++ (encodeUIntLE 4 message.eventExecWFirmShortCode
    ++ (encodeUIntLE 4 message.originalClientIdShortCode
    ++ (encodeUIntLE 4 message.originalExecWFirmShortCode
    ++ (Alpha.encode message.clearingAccount
    ++ (encodeUIntLE 4 message.lisTransactionId
    ++ (encodeUIntLE 4 message.parentExecId
    ++ (encodeUIntLE 4 message.parentSymbolIndex
    ++ (Alpha.encode message.tradeUniqueIdentifier
    ++ (Alpha.encode message.parentTradeUniqueIdentifier
    ++ (TradeBustNotificationShortCodesDetailsNonModifiableGroups.encode message.tradeBustNotificationShortCodesDetailsNonModifiableGroups
    ++ (TradeBustNotificationShortCodesDetailsModifiableGroups.encode message.tradeBustNotificationShortCodesDetailsModifiableGroups)))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeBustNotificationMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (oeSessionId, bytes) ← decodeUIntLE 8 bytes
  let (orderSide, bytes) ← decodeUInt 1 bytes
  let (bookOutTime, bytes) ← decodeUIntLE 8 bytes
  let (bookInTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (executionId, bytes) ← decodeUIntLE 4 bytes
  let (lastShares, bytes) ← decodeUIntLE 8 bytes
  let (lastTradedPx, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (miFidIndicators, bytes) ← decodeUIntLE 1 bytes
  let (clearingFirmId, bytes) ← Alpha.decode 8 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (oeginFromMember, bytes) ← decodeUIntLE 8 bytes
  let (executionPhase, bytes) ← decodeUInt 1 bytes
  let (tradeQualifier, bytes) ← decodeUIntLE 1 bytes
  let (counterpartFirmId, bytes) ← Alpha.decode 8 bytes
  let (orderType, bytes) ← decodeUInt 1 bytes
  let (timeInForceOptional, bytes) ← decodeUInt 1 bytes
  let (clearingInstructionOptional, bytes) ← decodeUIntLE 2 bytes
  let (technicalOrigin, bytes) ← decodeUInt 1 bytes
  let (freeText, bytes) ← Alpha.decode 18 bytes
  let (accountNumber, bytes) ← Alpha.decode 12 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (lpRoleOptional, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUIntLE 2 bytes
  let (originalInvestDecisWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (originalNonExecBrokerShortCode, bytes) ← decodeUIntLE 4 bytes
  let (eventClientIdShortCode, bytes) ← decodeUIntLE 4 bytes
  let (eventExecWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (originalClientIdShortCode, bytes) ← decodeUIntLE 4 bytes
  let (originalExecWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (clearingAccount, bytes) ← Alpha.decode 16 bytes
  let (lisTransactionId, bytes) ← decodeUIntLE 4 bytes
  let (parentExecId, bytes) ← decodeUIntLE 4 bytes
  let (parentSymbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (tradeUniqueIdentifier, bytes) ← Alpha.decode 16 bytes
  let (parentTradeUniqueIdentifier, bytes) ← Alpha.decode 16 bytes
  let (tradeBustNotificationShortCodesDetailsNonModifiableGroups, bytes) ← TradeBustNotificationShortCodesDetailsNonModifiableGroups.decode bytes
  let (tradeBustNotificationShortCodesDetailsModifiableGroups, bytes) ← TradeBustNotificationShortCodesDetailsModifiableGroups.decode bytes
  pure ({ msgSeqNum, produceTime, consumeTime, firmId, oeSessionId, orderSide, bookOutTime, bookInTime, symbolIndex, emm, executionId, lastShares, lastTradedPx, orderId, miFidIndicators, clearingFirmId, tradingCapacity, oeginFromMember, executionPhase, tradeQualifier, counterpartFirmId, orderType, timeInForceOptional, clearingInstructionOptional, technicalOrigin, freeText, accountNumber, accountType, lpRoleOptional, openClose, originalInvestDecisWFirmShortCode, originalNonExecBrokerShortCode, eventClientIdShortCode, eventExecWFirmShortCode, originalClientIdShortCode, originalExecWFirmShortCode, clearingAccount, lisTransactionId, parentExecId, parentSymbolIndex, tradeUniqueIdentifier, parentTradeUniqueIdentifier, tradeBustNotificationShortCodesDetailsNonModifiableGroups, tradeBustNotificationShortCodesDetailsModifiableGroups }, bytes)

theorem encode_length_pos (message : TradeBustNotificationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBustNotificationMessage) : (encode message).length ≤ 1771 := by
  have bound_tradeBustNotificationShortCodesDetailsNonModifiableGroups := TradeBustNotificationShortCodesDetailsNonModifiableGroups.encode_length_le message.tradeBustNotificationShortCodesDetailsNonModifiableGroups
  have bound_tradeBustNotificationShortCodesDetailsModifiableGroups := TradeBustNotificationShortCodesDetailsModifiableGroups.encode_length_le message.tradeBustNotificationShortCodesDetailsModifiableGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeBustNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeBustNotificationShortCodesDetailsNonModifiableGroups.decode_encode, some_bind]
  dsimp only
  rw [TradeBustNotificationShortCodesDetailsModifiableGroups.decode_encode, some_bind]
  rfl

end TradeBustNotificationMessage

/-- D C Quote Message Bid Quoterep Group: 68 bytes -/
structure DCQuoteMessageBidQuoterepGroup where
  bidSize : BitVec 64
  bidPx : BitVec 64
  bidQuotePriority : BitVec 64
  bidOrderId : BitVec 64
  buyRevisionFlag : BitVec 8
  bidErrorCode : BitVec 16
  bidOeSessionId : BitVec 64
  rfeAnswerOptional : BitVec 8
  bidLeavesQuantity : BitVec 64
  bidPreviousSize : BitVec 64
  bidPreviousPx : BitVec 64
  deriving DecidableEq, Repr

namespace DCQuoteMessageBidQuoterepGroup

def encode (message : DCQuoteMessageBidQuoterepGroup) : List UInt8 :=
  encodeUIntLE 8 message.bidSize
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.bidQuotePriority
    ++ (encodeUIntLE 8 message.bidOrderId
    ++ (encodeUInt 1 message.buyRevisionFlag
    ++ (encodeUIntLE 2 message.bidErrorCode
    ++ (encodeUIntLE 8 message.bidOeSessionId
    ++ (encodeUInt 1 message.rfeAnswerOptional
    ++ (encodeUIntLE 8 message.bidLeavesQuantity
    ++ (encodeUIntLE 8 message.bidPreviousSize
    ++ (encodeUIntLE 8 message.bidPreviousPx))))))))))

def decode (bytes : List UInt8) : Option (DCQuoteMessageBidQuoterepGroup × List UInt8) := do
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (bidQuotePriority, bytes) ← decodeUIntLE 8 bytes
  let (bidOrderId, bytes) ← decodeUIntLE 8 bytes
  let (buyRevisionFlag, bytes) ← decodeUInt 1 bytes
  let (bidErrorCode, bytes) ← decodeUIntLE 2 bytes
  let (bidOeSessionId, bytes) ← decodeUIntLE 8 bytes
  let (rfeAnswerOptional, bytes) ← decodeUInt 1 bytes
  let (bidLeavesQuantity, bytes) ← decodeUIntLE 8 bytes
  let (bidPreviousSize, bytes) ← decodeUIntLE 8 bytes
  let (bidPreviousPx, bytes) ← decodeUIntLE 8 bytes
  pure ({ bidSize, bidPx, bidQuotePriority, bidOrderId, buyRevisionFlag, bidErrorCode, bidOeSessionId, rfeAnswerOptional, bidLeavesQuantity, bidPreviousSize, bidPreviousPx }, bytes)

@[simp] theorem encode_length (message : DCQuoteMessageBidQuoterepGroup) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DCQuoteMessageBidQuoterepGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCQuoteMessageBidQuoterepGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DCQuoteMessageBidQuoterepGroup

/-- D C Quote Message Bid Quoterep Groups -/
structure DCQuoteMessageBidQuoterepGroups where
  blockLengthShort : BitVec 8
  dCQuoteMessageBidQuoterepGroup : Bounded 1 DCQuoteMessageBidQuoterepGroup
  deriving DecidableEq, Repr

namespace DCQuoteMessageBidQuoterepGroups

def encode (message : DCQuoteMessageBidQuoterepGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCQuoteMessageBidQuoterepGroup.val.length)
    ++ (encodeMany DCQuoteMessageBidQuoterepGroup.encode message.dCQuoteMessageBidQuoterepGroup.val))

def decode (bytes : List UInt8) : Option (DCQuoteMessageBidQuoterepGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCQuoteMessageBidQuoterepGroup_, bytes) ← decodeMany DCQuoteMessageBidQuoterepGroup.decode numInGroup.toNat bytes
  if fits_dCQuoteMessageBidQuoterepGroup : dCQuoteMessageBidQuoterepGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCQuoteMessageBidQuoterepGroup := ⟨dCQuoteMessageBidQuoterepGroup_, fits_dCQuoteMessageBidQuoterepGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCQuoteMessageBidQuoterepGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCQuoteMessageBidQuoterepGroups) : (encode message).length ≤ 17342 := by
  have bound_dCQuoteMessageBidQuoterepGroup := message.dCQuoteMessageBidQuoterepGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCQuoteMessageBidQuoterepGroup.encode 68 DCQuoteMessageBidQuoterepGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCQuoteMessageBidQuoterepGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCQuoteMessageBidQuoterepGroup.encode DCQuoteMessageBidQuoterepGroup.decode DCQuoteMessageBidQuoterepGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCQuoteMessageBidQuoterepGroup.length_lt]
  rfl

end DCQuoteMessageBidQuoterepGroups

/-- D C Quote Message Offer Quoterep Group: 68 bytes -/
structure DCQuoteMessageOfferQuoterepGroup where
  offerSize : BitVec 64
  offerPx : BitVec 64
  offerQuotePriority : BitVec 64
  offerOrderId : BitVec 64
  sellRevisionFlag : BitVec 8
  offerErrorCode : BitVec 16
  offerOeSessionId : BitVec 64
  rfeAnswerOptional : BitVec 8
  offerLeavesQuantity : BitVec 64
  offerPreviousSize : BitVec 64
  offerPreviousPx : BitVec 64
  deriving DecidableEq, Repr

namespace DCQuoteMessageOfferQuoterepGroup

def encode (message : DCQuoteMessageOfferQuoterepGroup) : List UInt8 :=
  encodeUIntLE 8 message.offerSize
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.offerQuotePriority
    ++ (encodeUIntLE 8 message.offerOrderId
    ++ (encodeUInt 1 message.sellRevisionFlag
    ++ (encodeUIntLE 2 message.offerErrorCode
    ++ (encodeUIntLE 8 message.offerOeSessionId
    ++ (encodeUInt 1 message.rfeAnswerOptional
    ++ (encodeUIntLE 8 message.offerLeavesQuantity
    ++ (encodeUIntLE 8 message.offerPreviousSize
    ++ (encodeUIntLE 8 message.offerPreviousPx))))))))))

def decode (bytes : List UInt8) : Option (DCQuoteMessageOfferQuoterepGroup × List UInt8) := do
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (offerQuotePriority, bytes) ← decodeUIntLE 8 bytes
  let (offerOrderId, bytes) ← decodeUIntLE 8 bytes
  let (sellRevisionFlag, bytes) ← decodeUInt 1 bytes
  let (offerErrorCode, bytes) ← decodeUIntLE 2 bytes
  let (offerOeSessionId, bytes) ← decodeUIntLE 8 bytes
  let (rfeAnswerOptional, bytes) ← decodeUInt 1 bytes
  let (offerLeavesQuantity, bytes) ← decodeUIntLE 8 bytes
  let (offerPreviousSize, bytes) ← decodeUIntLE 8 bytes
  let (offerPreviousPx, bytes) ← decodeUIntLE 8 bytes
  pure ({ offerSize, offerPx, offerQuotePriority, offerOrderId, sellRevisionFlag, offerErrorCode, offerOeSessionId, rfeAnswerOptional, offerLeavesQuantity, offerPreviousSize, offerPreviousPx }, bytes)

@[simp] theorem encode_length (message : DCQuoteMessageOfferQuoterepGroup) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DCQuoteMessageOfferQuoterepGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCQuoteMessageOfferQuoterepGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DCQuoteMessageOfferQuoterepGroup

/-- D C Quote Message Offer Quoterep Groups -/
structure DCQuoteMessageOfferQuoterepGroups where
  blockLengthShort : BitVec 8
  dCQuoteMessageOfferQuoterepGroup : Bounded 1 DCQuoteMessageOfferQuoterepGroup
  deriving DecidableEq, Repr

namespace DCQuoteMessageOfferQuoterepGroups

def encode (message : DCQuoteMessageOfferQuoterepGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCQuoteMessageOfferQuoterepGroup.val.length)
    ++ (encodeMany DCQuoteMessageOfferQuoterepGroup.encode message.dCQuoteMessageOfferQuoterepGroup.val))

def decode (bytes : List UInt8) : Option (DCQuoteMessageOfferQuoterepGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCQuoteMessageOfferQuoterepGroup_, bytes) ← decodeMany DCQuoteMessageOfferQuoterepGroup.decode numInGroup.toNat bytes
  if fits_dCQuoteMessageOfferQuoterepGroup : dCQuoteMessageOfferQuoterepGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCQuoteMessageOfferQuoterepGroup := ⟨dCQuoteMessageOfferQuoterepGroup_, fits_dCQuoteMessageOfferQuoterepGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCQuoteMessageOfferQuoterepGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCQuoteMessageOfferQuoterepGroups) : (encode message).length ≤ 17342 := by
  have bound_dCQuoteMessageOfferQuoterepGroup := message.dCQuoteMessageOfferQuoterepGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCQuoteMessageOfferQuoterepGroup.encode 68 DCQuoteMessageOfferQuoterepGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCQuoteMessageOfferQuoterepGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCQuoteMessageOfferQuoterepGroup.encode DCQuoteMessageOfferQuoterepGroup.decode DCQuoteMessageOfferQuoterepGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCQuoteMessageOfferQuoterepGroup.length_lt]
  rfl

end DCQuoteMessageOfferQuoterepGroups

/-- D C Quote Message Clearing Dataset Group: 51 bytes -/
structure DCQuoteMessageClearingDatasetGroup where
  clearingFirmIdOptional : Alpha 8
  clientId : Alpha 8
  accountNumber : Alpha 12
  technicalOrigin : BitVec 8
  openClose : BitVec 16
  clearingInstructionOptional : BitVec 16
  freeText : Alpha 18
  deriving DecidableEq, Repr

namespace DCQuoteMessageClearingDatasetGroup

def encode (message : DCQuoteMessageClearingDatasetGroup) : List UInt8 :=
  Alpha.encode message.clearingFirmIdOptional
    ++ (Alpha.encode message.clientId
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 1 message.technicalOrigin
    ++ (encodeUIntLE 2 message.openClose
    ++ (encodeUIntLE 2 message.clearingInstructionOptional
    ++ (Alpha.encode message.freeText))))))

def decode (bytes : List UInt8) : Option (DCQuoteMessageClearingDatasetGroup × List UInt8) := do
  let (clearingFirmIdOptional, bytes) ← Alpha.decode 8 bytes
  let (clientId, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 12 bytes
  let (technicalOrigin, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUIntLE 2 bytes
  let (clearingInstructionOptional, bytes) ← decodeUIntLE 2 bytes
  let (freeText, bytes) ← Alpha.decode 18 bytes
  pure ({ clearingFirmIdOptional, clientId, accountNumber, technicalOrigin, openClose, clearingInstructionOptional, freeText }, bytes)

@[simp] theorem encode_length (message : DCQuoteMessageClearingDatasetGroup) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : DCQuoteMessageClearingDatasetGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCQuoteMessageClearingDatasetGroup) (rest : List UInt8) :
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

end DCQuoteMessageClearingDatasetGroup

/-- D C Quote Message Clearing Dataset Groups -/
structure DCQuoteMessageClearingDatasetGroups where
  blockLengthShort : BitVec 8
  dCQuoteMessageClearingDatasetGroup : Bounded 1 DCQuoteMessageClearingDatasetGroup
  deriving DecidableEq, Repr

namespace DCQuoteMessageClearingDatasetGroups

def encode (message : DCQuoteMessageClearingDatasetGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCQuoteMessageClearingDatasetGroup.val.length)
    ++ (encodeMany DCQuoteMessageClearingDatasetGroup.encode message.dCQuoteMessageClearingDatasetGroup.val))

def decode (bytes : List UInt8) : Option (DCQuoteMessageClearingDatasetGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCQuoteMessageClearingDatasetGroup_, bytes) ← decodeMany DCQuoteMessageClearingDatasetGroup.decode numInGroup.toNat bytes
  if fits_dCQuoteMessageClearingDatasetGroup : dCQuoteMessageClearingDatasetGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCQuoteMessageClearingDatasetGroup := ⟨dCQuoteMessageClearingDatasetGroup_, fits_dCQuoteMessageClearingDatasetGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCQuoteMessageClearingDatasetGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCQuoteMessageClearingDatasetGroups) : (encode message).length ≤ 13007 := by
  have bound_dCQuoteMessageClearingDatasetGroup := message.dCQuoteMessageClearingDatasetGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCQuoteMessageClearingDatasetGroup.encode 51 DCQuoteMessageClearingDatasetGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCQuoteMessageClearingDatasetGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCQuoteMessageClearingDatasetGroup.encode DCQuoteMessageClearingDatasetGroup.decode DCQuoteMessageClearingDatasetGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCQuoteMessageClearingDatasetGroup.length_lt]
  rfl

end DCQuoteMessageClearingDatasetGroups

/-- D C Quote Message Non Modifiable Short Codes Group: 16 bytes -/
structure DCQuoteMessageNonModifiableShortCodesGroup where
  originalClientIdShortCode : BitVec 32
  originalExecWFirmShortCode : BitVec 32
  originalInvestDecisWFirmShortCode : BitVec 32
  originalNonExecBrokerShortCode : BitVec 32
  deriving DecidableEq, Repr

namespace DCQuoteMessageNonModifiableShortCodesGroup

def encode (message : DCQuoteMessageNonModifiableShortCodesGroup) : List UInt8 :=
  encodeUIntLE 4 message.originalClientIdShortCode
    ++ (encodeUIntLE 4 message.originalExecWFirmShortCode
    ++ (encodeUIntLE 4 message.originalInvestDecisWFirmShortCode
    ++ (encodeUIntLE 4 message.originalNonExecBrokerShortCode)))

def decode (bytes : List UInt8) : Option (DCQuoteMessageNonModifiableShortCodesGroup × List UInt8) := do
  let (originalClientIdShortCode, bytes) ← decodeUIntLE 4 bytes
  let (originalExecWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (originalInvestDecisWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (originalNonExecBrokerShortCode, bytes) ← decodeUIntLE 4 bytes
  pure ({ originalClientIdShortCode, originalExecWFirmShortCode, originalInvestDecisWFirmShortCode, originalNonExecBrokerShortCode }, bytes)

@[simp] theorem encode_length (message : DCQuoteMessageNonModifiableShortCodesGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DCQuoteMessageNonModifiableShortCodesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCQuoteMessageNonModifiableShortCodesGroup) (rest : List UInt8) :
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

end DCQuoteMessageNonModifiableShortCodesGroup

/-- D C Quote Message Non Modifiable Short Codes Groups -/
structure DCQuoteMessageNonModifiableShortCodesGroups where
  blockLengthShort : BitVec 8
  dCQuoteMessageNonModifiableShortCodesGroup : Bounded 1 DCQuoteMessageNonModifiableShortCodesGroup
  deriving DecidableEq, Repr

namespace DCQuoteMessageNonModifiableShortCodesGroups

def encode (message : DCQuoteMessageNonModifiableShortCodesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCQuoteMessageNonModifiableShortCodesGroup.val.length)
    ++ (encodeMany DCQuoteMessageNonModifiableShortCodesGroup.encode message.dCQuoteMessageNonModifiableShortCodesGroup.val))

def decode (bytes : List UInt8) : Option (DCQuoteMessageNonModifiableShortCodesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCQuoteMessageNonModifiableShortCodesGroup_, bytes) ← decodeMany DCQuoteMessageNonModifiableShortCodesGroup.decode numInGroup.toNat bytes
  if fits_dCQuoteMessageNonModifiableShortCodesGroup : dCQuoteMessageNonModifiableShortCodesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCQuoteMessageNonModifiableShortCodesGroup := ⟨dCQuoteMessageNonModifiableShortCodesGroup_, fits_dCQuoteMessageNonModifiableShortCodesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCQuoteMessageNonModifiableShortCodesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCQuoteMessageNonModifiableShortCodesGroups) : (encode message).length ≤ 4082 := by
  have bound_dCQuoteMessageNonModifiableShortCodesGroup := message.dCQuoteMessageNonModifiableShortCodesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCQuoteMessageNonModifiableShortCodesGroup.encode 16 DCQuoteMessageNonModifiableShortCodesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCQuoteMessageNonModifiableShortCodesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCQuoteMessageNonModifiableShortCodesGroup.encode DCQuoteMessageNonModifiableShortCodesGroup.decode DCQuoteMessageNonModifiableShortCodesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCQuoteMessageNonModifiableShortCodesGroup.length_lt]
  rfl

end DCQuoteMessageNonModifiableShortCodesGroups

/-- D C Quote Message Modifiable Short Codes Group: 8 bytes -/
structure DCQuoteMessageModifiableShortCodesGroup where
  eventClientIdShortCode : BitVec 32
  eventExecWFirmShortCode : BitVec 32
  deriving DecidableEq, Repr

namespace DCQuoteMessageModifiableShortCodesGroup

def encode (message : DCQuoteMessageModifiableShortCodesGroup) : List UInt8 :=
  encodeUIntLE 4 message.eventClientIdShortCode
    ++ (encodeUIntLE 4 message.eventExecWFirmShortCode)

def decode (bytes : List UInt8) : Option (DCQuoteMessageModifiableShortCodesGroup × List UInt8) := do
  let (eventClientIdShortCode, bytes) ← decodeUIntLE 4 bytes
  let (eventExecWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  pure ({ eventClientIdShortCode, eventExecWFirmShortCode }, bytes)

@[simp] theorem encode_length (message : DCQuoteMessageModifiableShortCodesGroup) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DCQuoteMessageModifiableShortCodesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCQuoteMessageModifiableShortCodesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DCQuoteMessageModifiableShortCodesGroup

/-- D C Quote Message Modifiable Short Codes Groups -/
structure DCQuoteMessageModifiableShortCodesGroups where
  blockLengthShort : BitVec 8
  dCQuoteMessageModifiableShortCodesGroup : Bounded 1 DCQuoteMessageModifiableShortCodesGroup
  deriving DecidableEq, Repr

namespace DCQuoteMessageModifiableShortCodesGroups

def encode (message : DCQuoteMessageModifiableShortCodesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCQuoteMessageModifiableShortCodesGroup.val.length)
    ++ (encodeMany DCQuoteMessageModifiableShortCodesGroup.encode message.dCQuoteMessageModifiableShortCodesGroup.val))

def decode (bytes : List UInt8) : Option (DCQuoteMessageModifiableShortCodesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCQuoteMessageModifiableShortCodesGroup_, bytes) ← decodeMany DCQuoteMessageModifiableShortCodesGroup.decode numInGroup.toNat bytes
  if fits_dCQuoteMessageModifiableShortCodesGroup : dCQuoteMessageModifiableShortCodesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCQuoteMessageModifiableShortCodesGroup := ⟨dCQuoteMessageModifiableShortCodesGroup_, fits_dCQuoteMessageModifiableShortCodesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCQuoteMessageModifiableShortCodesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCQuoteMessageModifiableShortCodesGroups) : (encode message).length ≤ 2042 := by
  have bound_dCQuoteMessageModifiableShortCodesGroup := message.dCQuoteMessageModifiableShortCodesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCQuoteMessageModifiableShortCodesGroup.encode 8 DCQuoteMessageModifiableShortCodesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCQuoteMessageModifiableShortCodesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCQuoteMessageModifiableShortCodesGroup.encode DCQuoteMessageModifiableShortCodesGroup.decode DCQuoteMessageModifiableShortCodesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCQuoteMessageModifiableShortCodesGroup.length_lt]
  rfl

end DCQuoteMessageModifiableShortCodesGroups

/-- Dc Quote Message -/
structure DcQuoteMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  bookIn : BitVec 64
  bookOutTime : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  eventId : BitVec 64
  clientOrderId : BitVec 64
  tradingCapacity : BitVec 8
  accountType : BitVec 8
  lpRole : BitVec 8
  miFidIndicators : BitVec 8
  rfeAnswer : BitVec 8
  firmId : Alpha 8
  executionInstructionOptional : BitVec 8
  stpid : BitVec 16
  dCQuoteMessageBidQuoterepGroups : DCQuoteMessageBidQuoterepGroups
  dCQuoteMessageOfferQuoterepGroups : DCQuoteMessageOfferQuoterepGroups
  dCQuoteMessageClearingDatasetGroups : DCQuoteMessageClearingDatasetGroups
  dCQuoteMessageNonModifiableShortCodesGroups : DCQuoteMessageNonModifiableShortCodesGroups
  dCQuoteMessageModifiableShortCodesGroups : DCQuoteMessageModifiableShortCodesGroups
  deriving DecidableEq, Repr

namespace DcQuoteMessage

def encode (message : DcQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTime
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.lpRole
    ++ (encodeUIntLE 1 message.miFidIndicators
    ++ (encodeUInt 1 message.rfeAnswer
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 1 message.executionInstructionOptional
    ++ (encodeUIntLE 2 message.stpid
    ++ (DCQuoteMessageBidQuoterepGroups.encode message.dCQuoteMessageBidQuoterepGroups
    ++ (DCQuoteMessageOfferQuoterepGroups.encode message.dCQuoteMessageOfferQuoterepGroups
    ++ (DCQuoteMessageClearingDatasetGroups.encode message.dCQuoteMessageClearingDatasetGroups
    ++ (DCQuoteMessageNonModifiableShortCodesGroups.encode message.dCQuoteMessageNonModifiableShortCodesGroups
    ++ (DCQuoteMessageModifiableShortCodesGroups.encode message.dCQuoteMessageModifiableShortCodesGroups)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (DcQuoteMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (lpRole, bytes) ← decodeUInt 1 bytes
  let (miFidIndicators, bytes) ← decodeUIntLE 1 bytes
  let (rfeAnswer, bytes) ← decodeUInt 1 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (executionInstructionOptional, bytes) ← decodeUIntLE 1 bytes
  let (stpid, bytes) ← decodeUIntLE 2 bytes
  let (dCQuoteMessageBidQuoterepGroups, bytes) ← DCQuoteMessageBidQuoterepGroups.decode bytes
  let (dCQuoteMessageOfferQuoterepGroups, bytes) ← DCQuoteMessageOfferQuoterepGroups.decode bytes
  let (dCQuoteMessageClearingDatasetGroups, bytes) ← DCQuoteMessageClearingDatasetGroups.decode bytes
  let (dCQuoteMessageNonModifiableShortCodesGroups, bytes) ← DCQuoteMessageNonModifiableShortCodesGroups.decode bytes
  let (dCQuoteMessageModifiableShortCodesGroups, bytes) ← DCQuoteMessageModifiableShortCodesGroups.decode bytes
  pure ({ msgSeqNum, produceTime, consumeTime, bookIn, bookOutTime, symbolIndex, emm, eventId, clientOrderId, tradingCapacity, accountType, lpRole, miFidIndicators, rfeAnswer, firmId, executionInstructionOptional, stpid, dCQuoteMessageBidQuoterepGroups, dCQuoteMessageOfferQuoterepGroups, dCQuoteMessageClearingDatasetGroups, dCQuoteMessageNonModifiableShortCodesGroups, dCQuoteMessageModifiableShortCodesGroups }, bytes)

theorem encode_length_pos (message : DcQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DcQuoteMessage) : (encode message).length ≤ 53888 := by
  have bound_dCQuoteMessageBidQuoterepGroups := DCQuoteMessageBidQuoterepGroups.encode_length_le message.dCQuoteMessageBidQuoterepGroups
  have bound_dCQuoteMessageOfferQuoterepGroups := DCQuoteMessageOfferQuoterepGroups.encode_length_le message.dCQuoteMessageOfferQuoterepGroups
  have bound_dCQuoteMessageClearingDatasetGroups := DCQuoteMessageClearingDatasetGroups.encode_length_le message.dCQuoteMessageClearingDatasetGroups
  have bound_dCQuoteMessageNonModifiableShortCodesGroups := DCQuoteMessageNonModifiableShortCodesGroups.encode_length_le message.dCQuoteMessageNonModifiableShortCodesGroups
  have bound_dCQuoteMessageModifiableShortCodesGroups := DCQuoteMessageModifiableShortCodesGroups.encode_length_le message.dCQuoteMessageModifiableShortCodesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : DcQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, DCQuoteMessageBidQuoterepGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DCQuoteMessageOfferQuoterepGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DCQuoteMessageClearingDatasetGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DCQuoteMessageNonModifiableShortCodesGroups.decode_encode, some_bind]
  dsimp only
  rw [DCQuoteMessageModifiableShortCodesGroups.decode_encode, some_bind]
  rfl

end DcQuoteMessage

/-- Dcafqrfe Message: 59 bytes -/
structure DcafqrfeMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  afqReason : BitVec 8
  bookOutTime : BitVec 64
  emm : BitVec 8
  eventId : BitVec 64
  symbolIndex : BitVec 32
  firmId : Alpha 8
  afqIndicator : BitVec 8
  oeSessionId : BitVec 64
  deriving DecidableEq, Repr

namespace DcafqrfeMessage

def encode (message : DcafqrfeMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUInt 1 message.afqReason
    ++ (encodeUIntLE 8 message.bookOutTime
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 1 message.afqIndicator
    ++ (encodeUIntLE 8 message.oeSessionId))))))))))

def decode (bytes : List UInt8) : Option (DcafqrfeMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (afqReason, bytes) ← decodeUInt 1 bytes
  let (bookOutTime, bytes) ← decodeUIntLE 8 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (afqIndicator, bytes) ← decodeUInt 1 bytes
  let (oeSessionId, bytes) ← decodeUIntLE 8 bytes
  pure ({ msgSeqNum, produceTime, consumeTime, afqReason, bookOutTime, emm, eventId, symbolIndex, firmId, afqIndicator, oeSessionId }, bytes)

@[simp] theorem encode_length (message : DcafqrfeMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DcafqrfeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcafqrfeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DcafqrfeMessage

/-- Dc Declaration New Message: 221 bytes -/
structure DcDeclarationNewMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  messageSendingTime : BitVec 64
  bookIn : BitVec 64
  bookOutTime : BitVec 64
  oeginFromMember : BitVec 64
  oegoutTimeToMe : BitVec 64
  eventId : BitVec 64
  declarationEventType : BitVec 8
  firmId : Alpha 8
  oeSessionId : BitVec 64
  accountType : BitVec 8
  clientOrderId : BitVec 64
  emm : BitVec 8
  declarationId : BitVec 64
  declarationStatus : BitVec 8
  priceOptional : BitVec 64
  quantityOptional : BitVec 64
  side : BitVec 8
  symbolIndex : BitVec 32
  operationType : BitVec 8
  crossOrderIndicator : BitVec 8
  enteringCounterparty : Alpha 8
  traderId : Alpha 16
  investorId : Alpha 16
  freeText : Alpha 18
  principalCode : Alpha 8
  clearingFirmIdOptional : Alpha 8
  clearingAccount : Alpha 16
  settlementPeriod : BitVec 8
  settlementFlag : BitVec 8
  guaranteeFlag : BitVec 8
  transactionPriceType : BitVec 8
  deriving DecidableEq, Repr

namespace DcDeclarationNewMessage

def encode (message : DcDeclarationNewMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 8 message.messageSendingTime
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTime
    ++ (encodeUIntLE 8 message.oeginFromMember
    ++ (encodeUIntLE 8 message.oegoutTimeToMe
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUInt 1 message.declarationEventType
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.oeSessionId
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.declarationId
    ++ (encodeUInt 1 message.declarationStatus
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.quantityOptional
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.operationType
    ++ (encodeUInt 1 message.crossOrderIndicator
    ++ (Alpha.encode message.enteringCounterparty
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.investorId
    ++ (Alpha.encode message.freeText
    ++ (Alpha.encode message.principalCode
    ++ (Alpha.encode message.clearingFirmIdOptional
    ++ (Alpha.encode message.clearingAccount
    ++ (encodeUInt 1 message.settlementPeriod
    ++ (encodeUInt 1 message.settlementFlag
    ++ (encodeUInt 1 message.guaranteeFlag
    ++ (encodeUInt 1 message.transactionPriceType)))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (DcDeclarationNewMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (messageSendingTime, bytes) ← decodeUIntLE 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTime, bytes) ← decodeUIntLE 8 bytes
  let (oeginFromMember, bytes) ← decodeUIntLE 8 bytes
  let (oegoutTimeToMe, bytes) ← decodeUIntLE 8 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (declarationEventType, bytes) ← decodeUInt 1 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (oeSessionId, bytes) ← decodeUIntLE 8 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (declarationId, bytes) ← decodeUIntLE 8 bytes
  let (declarationStatus, bytes) ← decodeUInt 1 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (quantityOptional, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (operationType, bytes) ← decodeUInt 1 bytes
  let (crossOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (enteringCounterparty, bytes) ← Alpha.decode 8 bytes
  let (traderId, bytes) ← Alpha.decode 16 bytes
  let (investorId, bytes) ← Alpha.decode 16 bytes
  let (freeText, bytes) ← Alpha.decode 18 bytes
  let (principalCode, bytes) ← Alpha.decode 8 bytes
  let (clearingFirmIdOptional, bytes) ← Alpha.decode 8 bytes
  let (clearingAccount, bytes) ← Alpha.decode 16 bytes
  let (settlementPeriod, bytes) ← decodeUInt 1 bytes
  let (settlementFlag, bytes) ← decodeUInt 1 bytes
  let (guaranteeFlag, bytes) ← decodeUInt 1 bytes
  let (transactionPriceType, bytes) ← decodeUInt 1 bytes
  pure ({ msgSeqNum, produceTime, consumeTime, messageSendingTime, bookIn, bookOutTime, oeginFromMember, oegoutTimeToMe, eventId, declarationEventType, firmId, oeSessionId, accountType, clientOrderId, emm, declarationId, declarationStatus, priceOptional, quantityOptional, side, symbolIndex, operationType, crossOrderIndicator, enteringCounterparty, traderId, investorId, freeText, principalCode, clearingFirmIdOptional, clearingAccount, settlementPeriod, settlementFlag, guaranteeFlag, transactionPriceType }, bytes)

@[simp] theorem encode_length (message : DcDeclarationNewMessage) : (encode message).length = 221 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DcDeclarationNewMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : DcDeclarationNewMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DcDeclarationNewMessage

/-- Dc Short Declaration Reject Message: 102 bytes -/
structure DcShortDeclarationRejectMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  messageSendingTime : BitVec 64
  bookIn : BitVec 64
  bookOutTime : BitVec 64
  oeginFromMember : BitVec 64
  oegoutTimeToMe : BitVec 64
  eventId : BitVec 64
  declarationEventType : BitVec 8
  firmId : Alpha 8
  clientOrderId : BitVec 64
  emm : BitVec 8
  declarationId : BitVec 64
  symbolIndex : BitVec 32
  errorCode : BitVec 16
  rejectedMessageId : BitVec 16
  deriving DecidableEq, Repr

namespace DcShortDeclarationRejectMessage

def encode (message : DcShortDeclarationRejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 8 message.messageSendingTime
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTime
    ++ (encodeUIntLE 8 message.oeginFromMember
    ++ (encodeUIntLE 8 message.oegoutTimeToMe
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUInt 1 message.declarationEventType
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.declarationId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 2 message.errorCode
    ++ (encodeUIntLE 2 message.rejectedMessageId))))))))))))))))

def decode (bytes : List UInt8) : Option (DcShortDeclarationRejectMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (messageSendingTime, bytes) ← decodeUIntLE 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTime, bytes) ← decodeUIntLE 8 bytes
  let (oeginFromMember, bytes) ← decodeUIntLE 8 bytes
  let (oegoutTimeToMe, bytes) ← decodeUIntLE 8 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (declarationEventType, bytes) ← decodeUInt 1 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (declarationId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (errorCode, bytes) ← decodeUIntLE 2 bytes
  let (rejectedMessageId, bytes) ← decodeUIntLE 2 bytes
  pure ({ msgSeqNum, produceTime, consumeTime, messageSendingTime, bookIn, bookOutTime, oeginFromMember, oegoutTimeToMe, eventId, declarationEventType, firmId, clientOrderId, emm, declarationId, symbolIndex, errorCode, rejectedMessageId }, bytes)

@[simp] theorem encode_length (message : DcShortDeclarationRejectMessage) : (encode message).length = 102 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DcShortDeclarationRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcShortDeclarationRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DcShortDeclarationRejectMessage

/-- Dc Short Declaration Cancel Message: 107 bytes -/
structure DcShortDeclarationCancelMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  messageSendingTime : BitVec 64
  bookIn : BitVec 64
  bookOutTime : BitVec 64
  oeginFromMember : BitVec 64
  oegoutTimeToMe : BitVec 64
  eventId : BitVec 64
  declarationEventType : BitVec 8
  firmId : Alpha 8
  oeSessionId : BitVec 64
  clientOrderId : BitVec 64
  emm : BitVec 8
  declarationId : BitVec 64
  symbolIndex : BitVec 32
  declarationKillReason : BitVec 8
  deriving DecidableEq, Repr

namespace DcShortDeclarationCancelMessage

def encode (message : DcShortDeclarationCancelMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 8 message.messageSendingTime
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTime
    ++ (encodeUIntLE 8 message.oeginFromMember
    ++ (encodeUIntLE 8 message.oegoutTimeToMe
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUInt 1 message.declarationEventType
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.oeSessionId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.declarationId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.declarationKillReason))))))))))))))))

def decode (bytes : List UInt8) : Option (DcShortDeclarationCancelMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (messageSendingTime, bytes) ← decodeUIntLE 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTime, bytes) ← decodeUIntLE 8 bytes
  let (oeginFromMember, bytes) ← decodeUIntLE 8 bytes
  let (oegoutTimeToMe, bytes) ← decodeUIntLE 8 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (declarationEventType, bytes) ← decodeUInt 1 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (oeSessionId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (declarationId, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (declarationKillReason, bytes) ← decodeUInt 1 bytes
  pure ({ msgSeqNum, produceTime, consumeTime, messageSendingTime, bookIn, bookOutTime, oeginFromMember, oegoutTimeToMe, eventId, declarationEventType, firmId, oeSessionId, clientOrderId, emm, declarationId, symbolIndex, declarationKillReason }, bytes)

@[simp] theorem encode_length (message : DcShortDeclarationCancelMessage) : (encode message).length = 107 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DcShortDeclarationCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcShortDeclarationCancelMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DcShortDeclarationCancelMessage

/-- D C Short Trade Declaration Message Short Trade Declarations Group: 139 bytes -/
structure DCShortTradeDeclarationMessageShortTradeDeclarationsGroup where
  declarationId : BitVec 64
  priceOptional : BitVec 64
  quantityOptional : BitVec 64
  operationType : BitVec 8
  side : BitVec 8
  firmId : Alpha 8
  oePartitionId : BitVec 16
  logicalAccessId : BitVec 32
  bookIn : BitVec 64
  traderId : Alpha 16
  investorId : Alpha 16
  principalCode : Alpha 8
  clearingFirmIdOptional : Alpha 8
  clearingAccount : Alpha 16
  accountType : BitVec 8
  clientOrderId : BitVec 64
  freeText : Alpha 18
  deriving DecidableEq, Repr

namespace DCShortTradeDeclarationMessageShortTradeDeclarationsGroup

def encode (message : DCShortTradeDeclarationMessageShortTradeDeclarationsGroup) : List UInt8 :=
  encodeUIntLE 8 message.declarationId
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.quantityOptional
    ++ (encodeUInt 1 message.operationType
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 2 message.oePartitionId
    ++ (encodeUIntLE 4 message.logicalAccessId
    ++ (encodeUIntLE 8 message.bookIn
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.investorId
    ++ (Alpha.encode message.principalCode
    ++ (Alpha.encode message.clearingFirmIdOptional
    ++ (Alpha.encode message.clearingAccount
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (Alpha.encode message.freeText))))))))))))))))

def decode (bytes : List UInt8) : Option (DCShortTradeDeclarationMessageShortTradeDeclarationsGroup × List UInt8) := do
  let (declarationId, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (quantityOptional, bytes) ← decodeUIntLE 8 bytes
  let (operationType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (oePartitionId, bytes) ← decodeUIntLE 2 bytes
  let (logicalAccessId, bytes) ← decodeUIntLE 4 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (traderId, bytes) ← Alpha.decode 16 bytes
  let (investorId, bytes) ← Alpha.decode 16 bytes
  let (principalCode, bytes) ← Alpha.decode 8 bytes
  let (clearingFirmIdOptional, bytes) ← Alpha.decode 8 bytes
  let (clearingAccount, bytes) ← Alpha.decode 16 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (freeText, bytes) ← Alpha.decode 18 bytes
  pure ({ declarationId, priceOptional, quantityOptional, operationType, side, firmId, oePartitionId, logicalAccessId, bookIn, traderId, investorId, principalCode, clearingFirmIdOptional, clearingAccount, accountType, clientOrderId, freeText }, bytes)

@[simp] theorem encode_length (message : DCShortTradeDeclarationMessageShortTradeDeclarationsGroup) : (encode message).length = 139 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DCShortTradeDeclarationMessageShortTradeDeclarationsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCShortTradeDeclarationMessageShortTradeDeclarationsGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DCShortTradeDeclarationMessageShortTradeDeclarationsGroup

/-- D C Short Trade Declaration Message Short Trade Declarations Groups -/
structure DCShortTradeDeclarationMessageShortTradeDeclarationsGroups where
  blockLengthShort : BitVec 8
  dCShortTradeDeclarationMessageShortTradeDeclarationsGroup : Bounded 1 DCShortTradeDeclarationMessageShortTradeDeclarationsGroup
  deriving DecidableEq, Repr

namespace DCShortTradeDeclarationMessageShortTradeDeclarationsGroups

def encode (message : DCShortTradeDeclarationMessageShortTradeDeclarationsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCShortTradeDeclarationMessageShortTradeDeclarationsGroup.val.length)
    ++ (encodeMany DCShortTradeDeclarationMessageShortTradeDeclarationsGroup.encode message.dCShortTradeDeclarationMessageShortTradeDeclarationsGroup.val))

def decode (bytes : List UInt8) : Option (DCShortTradeDeclarationMessageShortTradeDeclarationsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCShortTradeDeclarationMessageShortTradeDeclarationsGroup_, bytes) ← decodeMany DCShortTradeDeclarationMessageShortTradeDeclarationsGroup.decode numInGroup.toNat bytes
  if fits_dCShortTradeDeclarationMessageShortTradeDeclarationsGroup : dCShortTradeDeclarationMessageShortTradeDeclarationsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCShortTradeDeclarationMessageShortTradeDeclarationsGroup := ⟨dCShortTradeDeclarationMessageShortTradeDeclarationsGroup_, fits_dCShortTradeDeclarationMessageShortTradeDeclarationsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCShortTradeDeclarationMessageShortTradeDeclarationsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCShortTradeDeclarationMessageShortTradeDeclarationsGroups) : (encode message).length ≤ 35447 := by
  have bound_dCShortTradeDeclarationMessageShortTradeDeclarationsGroup := message.dCShortTradeDeclarationMessageShortTradeDeclarationsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCShortTradeDeclarationMessageShortTradeDeclarationsGroup.encode 139 DCShortTradeDeclarationMessageShortTradeDeclarationsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCShortTradeDeclarationMessageShortTradeDeclarationsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCShortTradeDeclarationMessageShortTradeDeclarationsGroup.encode DCShortTradeDeclarationMessageShortTradeDeclarationsGroup.decode DCShortTradeDeclarationMessageShortTradeDeclarationsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCShortTradeDeclarationMessageShortTradeDeclarationsGroup.length_lt]
  rfl

end DCShortTradeDeclarationMessageShortTradeDeclarationsGroups

/-- Dc Short Trade Declaration Message -/
structure DcShortTradeDeclarationMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  eventId : BitVec 64
  emm : BitVec 8
  symbolIndex : BitVec 32
  executionId : BitVec 32
  crossOrderIndicator : BitVec 8
  tradeTime : BitVec 64
  publicationTime : BitVec 64
  sessionOptional : BitVec 8
  tradeType : BitVec 8
  settlementPeriodOptional : BitVec 8
  settlementFlagOptional : BitVec 8
  guaranteeFlagOptional : BitVec 8
  dCShortTradeDeclarationMessageShortTradeDeclarationsGroups : DCShortTradeDeclarationMessageShortTradeDeclarationsGroups
  deriving DecidableEq, Repr

namespace DcShortTradeDeclarationMessage

def encode (message : DcShortTradeDeclarationMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.executionId
    ++ (encodeUInt 1 message.crossOrderIndicator
    ++ (encodeUIntLE 8 message.tradeTime
    ++ (encodeUIntLE 8 message.publicationTime
    ++ (encodeUInt 1 message.sessionOptional
    ++ (encodeUInt 1 message.tradeType
    ++ (encodeUInt 1 message.settlementPeriodOptional
    ++ (encodeUInt 1 message.settlementFlagOptional
    ++ (encodeUInt 1 message.guaranteeFlagOptional
    ++ (DCShortTradeDeclarationMessageShortTradeDeclarationsGroups.encode message.dCShortTradeDeclarationMessageShortTradeDeclarationsGroups)))))))))))))))

def decode (bytes : List UInt8) : Option (DcShortTradeDeclarationMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (executionId, bytes) ← decodeUIntLE 4 bytes
  let (crossOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (tradeTime, bytes) ← decodeUIntLE 8 bytes
  let (publicationTime, bytes) ← decodeUIntLE 8 bytes
  let (sessionOptional, bytes) ← decodeUInt 1 bytes
  let (tradeType, bytes) ← decodeUInt 1 bytes
  let (settlementPeriodOptional, bytes) ← decodeUInt 1 bytes
  let (settlementFlagOptional, bytes) ← decodeUInt 1 bytes
  let (guaranteeFlagOptional, bytes) ← decodeUInt 1 bytes
  let (dCShortTradeDeclarationMessageShortTradeDeclarationsGroups, bytes) ← DCShortTradeDeclarationMessageShortTradeDeclarationsGroups.decode bytes
  pure ({ msgSeqNum, produceTime, consumeTime, eventId, emm, symbolIndex, executionId, crossOrderIndicator, tradeTime, publicationTime, sessionOptional, tradeType, settlementPeriodOptional, settlementFlagOptional, guaranteeFlagOptional, dCShortTradeDeclarationMessageShortTradeDeclarationsGroups }, bytes)

theorem encode_length_pos (message : DcShortTradeDeclarationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DcShortTradeDeclarationMessage) : (encode message).length ≤ 35506 := by
  have bound_dCShortTradeDeclarationMessageShortTradeDeclarationsGroups := DCShortTradeDeclarationMessageShortTradeDeclarationsGroups.encode_length_le message.dCShortTradeDeclarationMessageShortTradeDeclarationsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : DcShortTradeDeclarationMessage) (rest : List UInt8) :
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
  rw [DCShortTradeDeclarationMessageShortTradeDeclarationsGroups.decode_encode, some_bind]
  rfl

end DcShortTradeDeclarationMessage

/-- Dc Short Trade Declaration Cancellation Message: 61 bytes -/
structure DcShortTradeDeclarationCancellationMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  bookIn : BitVec 64
  eventId : BitVec 64
  emm : BitVec 8
  executionId : BitVec 32
  symbolIndex : BitVec 32
  price : BitVec 64
  quantity : BitVec 64
  deriving DecidableEq, Repr

namespace DcShortTradeDeclarationCancellationMessage

def encode (message : DcShortTradeDeclarationCancellationMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 4 message.executionId
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quantity)))))))))

def decode (bytes : List UInt8) : Option (DcShortTradeDeclarationCancellationMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (executionId, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  pure ({ msgSeqNum, produceTime, consumeTime, bookIn, eventId, emm, executionId, symbolIndex, price, quantity }, bytes)

@[simp] theorem encode_length (message : DcShortTradeDeclarationCancellationMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DcShortTradeDeclarationCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcShortTradeDeclarationCancellationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DcShortTradeDeclarationCancellationMessage

/-- Dc Trade Bust Declaration Message: 208 bytes -/
structure DcTradeBustDeclarationMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  messageSendingTime : BitVec 64
  bookIn : BitVec 64
  bookOutTime : BitVec 64
  oeginFromMember : BitVec 64
  oegoutTimeToMe : BitVec 64
  eventId : BitVec 64
  declarationEventType : BitVec 8
  firmId : Alpha 8
  oeSessionId : BitVec 64
  accountType : BitVec 8
  clientOrderId : BitVec 64
  emm : BitVec 8
  declarationId : BitVec 64
  declarationStatus : BitVec 8
  priceOptional : BitVec 64
  quantityOptional : BitVec 64
  side : BitVec 8
  symbolIndex : BitVec 32
  operationType : BitVec 8
  enteringCounterparty : Alpha 8
  traderId : Alpha 16
  investorId : Alpha 16
  freeText : Alpha 18
  clearingFirmIdOptional : Alpha 8
  clearingAccount : Alpha 16
  deriving DecidableEq, Repr

namespace DcTradeBustDeclarationMessage

def encode (message : DcTradeBustDeclarationMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 8 message.messageSendingTime
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTime
    ++ (encodeUIntLE 8 message.oeginFromMember
    ++ (encodeUIntLE 8 message.oegoutTimeToMe
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUInt 1 message.declarationEventType
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 8 message.oeSessionId
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.declarationId
    ++ (encodeUInt 1 message.declarationStatus
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.quantityOptional
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.operationType
    ++ (Alpha.encode message.enteringCounterparty
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.investorId
    ++ (Alpha.encode message.freeText
    ++ (Alpha.encode message.clearingFirmIdOptional
    ++ (Alpha.encode message.clearingAccount)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (DcTradeBustDeclarationMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (messageSendingTime, bytes) ← decodeUIntLE 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTime, bytes) ← decodeUIntLE 8 bytes
  let (oeginFromMember, bytes) ← decodeUIntLE 8 bytes
  let (oegoutTimeToMe, bytes) ← decodeUIntLE 8 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (declarationEventType, bytes) ← decodeUInt 1 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (oeSessionId, bytes) ← decodeUIntLE 8 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (declarationId, bytes) ← decodeUIntLE 8 bytes
  let (declarationStatus, bytes) ← decodeUInt 1 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (quantityOptional, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (operationType, bytes) ← decodeUInt 1 bytes
  let (enteringCounterparty, bytes) ← Alpha.decode 8 bytes
  let (traderId, bytes) ← Alpha.decode 16 bytes
  let (investorId, bytes) ← Alpha.decode 16 bytes
  let (freeText, bytes) ← Alpha.decode 18 bytes
  let (clearingFirmIdOptional, bytes) ← Alpha.decode 8 bytes
  let (clearingAccount, bytes) ← Alpha.decode 16 bytes
  pure ({ msgSeqNum, produceTime, consumeTime, messageSendingTime, bookIn, bookOutTime, oeginFromMember, oegoutTimeToMe, eventId, declarationEventType, firmId, oeSessionId, accountType, clientOrderId, emm, declarationId, declarationStatus, priceOptional, quantityOptional, side, symbolIndex, operationType, enteringCounterparty, traderId, investorId, freeText, clearingFirmIdOptional, clearingAccount }, bytes)

@[simp] theorem encode_length (message : DcTradeBustDeclarationMessage) : (encode message).length = 208 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DcTradeBustDeclarationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : DcTradeBustDeclarationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DcTradeBustDeclarationMessage

/-- D C Trade Message Matched Orders Group: 140 bytes -/
structure DCTradeMessageMatchedOrdersGroup where
  orderId : BitVec 64
  orderSide : BitVec 8
  orderType : BitVec 8
  timeInForce : BitVec 8
  orderPx : BitVec 64
  clientId : Alpha 8
  technicalOrigin : BitVec 8
  openClose : BitVec 16
  clientOrderId : BitVec 64
  firmId : Alpha 8
  oePartitionIdOptional : BitVec 16
  logicalAccessIdOptional : BitVec 32
  bookInOptional : BitVec 64
  tradeQualifierOptional : BitVec 8
  accountTypeInternalOptional : BitVec 8
  lpRoleOptional : BitVec 8
  clearingAccount : Alpha 16
  freeText : Alpha 18
  clearingFirmIdOptional : Alpha 8
  traderId : Alpha 16
  originalInvestorId : Alpha 16
  crossOrderIndicatorOptional : BitVec 8
  clearingInstruction : BitVec 16
  deriving DecidableEq, Repr

namespace DCTradeMessageMatchedOrdersGroup

def encode (message : DCTradeMessageMatchedOrdersGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUInt 1 message.orderSide
    ++ (encodeUInt 1 message.orderType
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUIntLE 8 message.orderPx
    ++ (Alpha.encode message.clientId
    ++ (encodeUInt 1 message.technicalOrigin
    ++ (encodeUIntLE 2 message.openClose
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 2 message.oePartitionIdOptional
    ++ (encodeUIntLE 4 message.logicalAccessIdOptional
    ++ (encodeUIntLE 8 message.bookInOptional
    ++ (encodeUIntLE 1 message.tradeQualifierOptional
    ++ (encodeUInt 1 message.accountTypeInternalOptional
    ++ (encodeUInt 1 message.lpRoleOptional
    ++ (Alpha.encode message.clearingAccount
    ++ (Alpha.encode message.freeText
    ++ (Alpha.encode message.clearingFirmIdOptional
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.originalInvestorId
    ++ (encodeUInt 1 message.crossOrderIndicatorOptional
    ++ (encodeUIntLE 2 message.clearingInstruction))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (DCTradeMessageMatchedOrdersGroup × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (orderSide, bytes) ← decodeUInt 1 bytes
  let (orderType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (orderPx, bytes) ← decodeUIntLE 8 bytes
  let (clientId, bytes) ← Alpha.decode 8 bytes
  let (technicalOrigin, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUIntLE 2 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (oePartitionIdOptional, bytes) ← decodeUIntLE 2 bytes
  let (logicalAccessIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (bookInOptional, bytes) ← decodeUIntLE 8 bytes
  let (tradeQualifierOptional, bytes) ← decodeUIntLE 1 bytes
  let (accountTypeInternalOptional, bytes) ← decodeUInt 1 bytes
  let (lpRoleOptional, bytes) ← decodeUInt 1 bytes
  let (clearingAccount, bytes) ← Alpha.decode 16 bytes
  let (freeText, bytes) ← Alpha.decode 18 bytes
  let (clearingFirmIdOptional, bytes) ← Alpha.decode 8 bytes
  let (traderId, bytes) ← Alpha.decode 16 bytes
  let (originalInvestorId, bytes) ← Alpha.decode 16 bytes
  let (crossOrderIndicatorOptional, bytes) ← decodeUInt 1 bytes
  let (clearingInstruction, bytes) ← decodeUIntLE 2 bytes
  pure ({ orderId, orderSide, orderType, timeInForce, orderPx, clientId, technicalOrigin, openClose, clientOrderId, firmId, oePartitionIdOptional, logicalAccessIdOptional, bookInOptional, tradeQualifierOptional, accountTypeInternalOptional, lpRoleOptional, clearingAccount, freeText, clearingFirmIdOptional, traderId, originalInvestorId, crossOrderIndicatorOptional, clearingInstruction }, bytes)

@[simp] theorem encode_length (message : DCTradeMessageMatchedOrdersGroup) : (encode message).length = 140 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DCTradeMessageMatchedOrdersGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCTradeMessageMatchedOrdersGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DCTradeMessageMatchedOrdersGroup

/-- D C Trade Message Matched Orders Groups -/
structure DCTradeMessageMatchedOrdersGroups where
  blockLengthShort : BitVec 8
  dCTradeMessageMatchedOrdersGroup : Bounded 1 DCTradeMessageMatchedOrdersGroup
  deriving DecidableEq, Repr

namespace DCTradeMessageMatchedOrdersGroups

def encode (message : DCTradeMessageMatchedOrdersGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCTradeMessageMatchedOrdersGroup.val.length)
    ++ (encodeMany DCTradeMessageMatchedOrdersGroup.encode message.dCTradeMessageMatchedOrdersGroup.val))

def decode (bytes : List UInt8) : Option (DCTradeMessageMatchedOrdersGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCTradeMessageMatchedOrdersGroup_, bytes) ← decodeMany DCTradeMessageMatchedOrdersGroup.decode numInGroup.toNat bytes
  if fits_dCTradeMessageMatchedOrdersGroup : dCTradeMessageMatchedOrdersGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCTradeMessageMatchedOrdersGroup := ⟨dCTradeMessageMatchedOrdersGroup_, fits_dCTradeMessageMatchedOrdersGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCTradeMessageMatchedOrdersGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCTradeMessageMatchedOrdersGroups) : (encode message).length ≤ 35702 := by
  have bound_dCTradeMessageMatchedOrdersGroup := message.dCTradeMessageMatchedOrdersGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCTradeMessageMatchedOrdersGroup.encode 140 DCTradeMessageMatchedOrdersGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCTradeMessageMatchedOrdersGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCTradeMessageMatchedOrdersGroup.encode DCTradeMessageMatchedOrdersGroup.decode DCTradeMessageMatchedOrdersGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCTradeMessageMatchedOrdersGroup.length_lt]
  rfl

end DCTradeMessageMatchedOrdersGroups

/-- D C Trade Message Matched Declarations Group: 124 bytes -/
structure DCTradeMessageMatchedDeclarationsGroup where
  declarationId : BitVec 64
  side : BitVec 8
  operationType : BitVec 8
  firmId : Alpha 8
  oePartitionIdOptional : BitVec 16
  logicalAccessIdOptional : BitVec 32
  bookInOptional : BitVec 64
  accountTypeOptional : BitVec 8
  clientOrderId : BitVec 64
  freeText : Alpha 18
  clearingFirmIdOptional : Alpha 8
  clearingAccount : Alpha 16
  principalCode : Alpha 8
  crossOrderIndicatorOptional : BitVec 8
  traderId : Alpha 16
  investorId : Alpha 16
  deriving DecidableEq, Repr

namespace DCTradeMessageMatchedDeclarationsGroup

def encode (message : DCTradeMessageMatchedDeclarationsGroup) : List UInt8 :=
  encodeUIntLE 8 message.declarationId
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.operationType
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 2 message.oePartitionIdOptional
    ++ (encodeUIntLE 4 message.logicalAccessIdOptional
    ++ (encodeUIntLE 8 message.bookInOptional
    ++ (encodeUInt 1 message.accountTypeOptional
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (Alpha.encode message.freeText
    ++ (Alpha.encode message.clearingFirmIdOptional
    ++ (Alpha.encode message.clearingAccount
    ++ (Alpha.encode message.principalCode
    ++ (encodeUInt 1 message.crossOrderIndicatorOptional
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.investorId)))))))))))))))

def decode (bytes : List UInt8) : Option (DCTradeMessageMatchedDeclarationsGroup × List UInt8) := do
  let (declarationId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (operationType, bytes) ← decodeUInt 1 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (oePartitionIdOptional, bytes) ← decodeUIntLE 2 bytes
  let (logicalAccessIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (bookInOptional, bytes) ← decodeUIntLE 8 bytes
  let (accountTypeOptional, bytes) ← decodeUInt 1 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (freeText, bytes) ← Alpha.decode 18 bytes
  let (clearingFirmIdOptional, bytes) ← Alpha.decode 8 bytes
  let (clearingAccount, bytes) ← Alpha.decode 16 bytes
  let (principalCode, bytes) ← Alpha.decode 8 bytes
  let (crossOrderIndicatorOptional, bytes) ← decodeUInt 1 bytes
  let (traderId, bytes) ← Alpha.decode 16 bytes
  let (investorId, bytes) ← Alpha.decode 16 bytes
  pure ({ declarationId, side, operationType, firmId, oePartitionIdOptional, logicalAccessIdOptional, bookInOptional, accountTypeOptional, clientOrderId, freeText, clearingFirmIdOptional, clearingAccount, principalCode, crossOrderIndicatorOptional, traderId, investorId }, bytes)

@[simp] theorem encode_length (message : DCTradeMessageMatchedDeclarationsGroup) : (encode message).length = 124 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DCTradeMessageMatchedDeclarationsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCTradeMessageMatchedDeclarationsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DCTradeMessageMatchedDeclarationsGroup

/-- D C Trade Message Matched Declarations Groups -/
structure DCTradeMessageMatchedDeclarationsGroups where
  blockLengthShort : BitVec 8
  dCTradeMessageMatchedDeclarationsGroup : Bounded 1 DCTradeMessageMatchedDeclarationsGroup
  deriving DecidableEq, Repr

namespace DCTradeMessageMatchedDeclarationsGroups

def encode (message : DCTradeMessageMatchedDeclarationsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCTradeMessageMatchedDeclarationsGroup.val.length)
    ++ (encodeMany DCTradeMessageMatchedDeclarationsGroup.encode message.dCTradeMessageMatchedDeclarationsGroup.val))

def decode (bytes : List UInt8) : Option (DCTradeMessageMatchedDeclarationsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCTradeMessageMatchedDeclarationsGroup_, bytes) ← decodeMany DCTradeMessageMatchedDeclarationsGroup.decode numInGroup.toNat bytes
  if fits_dCTradeMessageMatchedDeclarationsGroup : dCTradeMessageMatchedDeclarationsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCTradeMessageMatchedDeclarationsGroup := ⟨dCTradeMessageMatchedDeclarationsGroup_, fits_dCTradeMessageMatchedDeclarationsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCTradeMessageMatchedDeclarationsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCTradeMessageMatchedDeclarationsGroups) : (encode message).length ≤ 31622 := by
  have bound_dCTradeMessageMatchedDeclarationsGroup := message.dCTradeMessageMatchedDeclarationsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCTradeMessageMatchedDeclarationsGroup.encode 124 DCTradeMessageMatchedDeclarationsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCTradeMessageMatchedDeclarationsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCTradeMessageMatchedDeclarationsGroup.encode DCTradeMessageMatchedDeclarationsGroup.decode DCTradeMessageMatchedDeclarationsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCTradeMessageMatchedDeclarationsGroup.length_lt]
  rfl

end DCTradeMessageMatchedDeclarationsGroups

/-- Dc Trade Message -/
structure DcTradeMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  eventId : BitVec 64
  executionId : BitVec 32
  quantity : BitVec 64
  priceOptional : BitVec 64
  tradeTime : BitVec 64
  publicationTime : BitVec 64
  sessionOptional : BitVec 8
  execPhase : BitVec 8
  transparencyIndicator : BitVec 8
  tradeQualifier : BitVec 8
  settlementPeriodOptional : BitVec 8
  settlementFlagOptional : BitVec 8
  guaranteeFlagOptional : BitVec 8
  counterpartyReasonType : BitVec 8
  symbolIndex : BitVec 32
  emm : BitVec 8
  tradeType : BitVec 8
  dCTradeMessageMatchedOrdersGroups : DCTradeMessageMatchedOrdersGroups
  dCTradeMessageMatchedDeclarationsGroups : DCTradeMessageMatchedDeclarationsGroups
  deriving DecidableEq, Repr

namespace DcTradeMessage

def encode (message : DcTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUIntLE 4 message.executionId
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.tradeTime
    ++ (encodeUIntLE 8 message.publicationTime
    ++ (encodeUInt 1 message.sessionOptional
    ++ (encodeUInt 1 message.execPhase
    ++ (encodeUInt 1 message.transparencyIndicator
    ++ (encodeUIntLE 1 message.tradeQualifier
    ++ (encodeUInt 1 message.settlementPeriodOptional
    ++ (encodeUInt 1 message.settlementFlagOptional
    ++ (encodeUInt 1 message.guaranteeFlagOptional
    ++ (encodeUInt 1 message.counterpartyReasonType
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.tradeType
    ++ (DCTradeMessageMatchedOrdersGroups.encode message.dCTradeMessageMatchedOrdersGroups
    ++ (DCTradeMessageMatchedDeclarationsGroups.encode message.dCTradeMessageMatchedDeclarationsGroups)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (DcTradeMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (executionId, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (tradeTime, bytes) ← decodeUIntLE 8 bytes
  let (publicationTime, bytes) ← decodeUIntLE 8 bytes
  let (sessionOptional, bytes) ← decodeUInt 1 bytes
  let (execPhase, bytes) ← decodeUInt 1 bytes
  let (transparencyIndicator, bytes) ← decodeUInt 1 bytes
  let (tradeQualifier, bytes) ← decodeUIntLE 1 bytes
  let (settlementPeriodOptional, bytes) ← decodeUInt 1 bytes
  let (settlementFlagOptional, bytes) ← decodeUInt 1 bytes
  let (guaranteeFlagOptional, bytes) ← decodeUInt 1 bytes
  let (counterpartyReasonType, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (tradeType, bytes) ← decodeUInt 1 bytes
  let (dCTradeMessageMatchedOrdersGroups, bytes) ← DCTradeMessageMatchedOrdersGroups.decode bytes
  let (dCTradeMessageMatchedDeclarationsGroups, bytes) ← DCTradeMessageMatchedDeclarationsGroups.decode bytes
  pure ({ msgSeqNum, produceTime, consumeTime, eventId, executionId, quantity, priceOptional, tradeTime, publicationTime, sessionOptional, execPhase, transparencyIndicator, tradeQualifier, settlementPeriodOptional, settlementFlagOptional, guaranteeFlagOptional, counterpartyReasonType, symbolIndex, emm, tradeType, dCTradeMessageMatchedOrdersGroups, dCTradeMessageMatchedDeclarationsGroups }, bytes)

theorem encode_length_pos (message : DcTradeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DcTradeMessage) : (encode message).length ≤ 67402 := by
  have bound_dCTradeMessageMatchedOrdersGroups := DCTradeMessageMatchedOrdersGroups.encode_length_le message.dCTradeMessageMatchedOrdersGroups
  have bound_dCTradeMessageMatchedDeclarationsGroups := DCTradeMessageMatchedDeclarationsGroups.encode_length_le message.dCTradeMessageMatchedDeclarationsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : DcTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, DCTradeMessageMatchedOrdersGroups.decode_encode, some_bind]
  dsimp only
  rw [DCTradeMessageMatchedDeclarationsGroups.decode_encode, some_bind]
  rfl

end DcTradeMessage

/-- Dc Short Declaration Fill Message: 228 bytes -/
structure DcShortDeclarationFillMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  messageSendingTime : BitVec 64
  bookIn : BitVec 64
  bookOutTime : BitVec 64
  oeginFromMember : BitVec 64
  oegoutTimeToMe : BitVec 64
  operationType : BitVec 8
  declarationEventType : BitVec 8
  declarationStatus : BitVec 8
  eventId : BitVec 64
  emm : BitVec 8
  symbolIndex : BitVec 32
  declarationId : BitVec 64
  price : BitVec 64
  quantity : BitVec 64
  side : BitVec 8
  crossOrderIndicator : BitVec 8
  tradeTime : BitVec 64
  enteringCounterparty : Alpha 8
  sessionOptional : BitVec 8
  tradeType : BitVec 8
  firmId : Alpha 8
  oePartitionId : BitVec 16
  logicalAccessId : BitVec 32
  traderId : Alpha 16
  investorId : Alpha 16
  principalCode : Alpha 8
  clearingFirmIdOptional : Alpha 8
  clearingAccount : Alpha 16
  accountType : BitVec 8
  clientOrderId : BitVec 64
  freeText : Alpha 18
  settlementPeriodOptional : BitVec 8
  settlementFlagOptional : BitVec 8
  guaranteeFlagOptional : BitVec 8
  deriving DecidableEq, Repr

namespace DcShortDeclarationFillMessage

def encode (message : DcShortDeclarationFillMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 8 message.messageSendingTime
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTime
    ++ (encodeUIntLE 8 message.oeginFromMember
    ++ (encodeUIntLE 8 message.oegoutTimeToMe
    ++ (encodeUInt 1 message.operationType
    ++ (encodeUInt 1 message.declarationEventType
    ++ (encodeUInt 1 message.declarationStatus
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.declarationId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.crossOrderIndicator
    ++ (encodeUIntLE 8 message.tradeTime
    ++ (Alpha.encode message.enteringCounterparty
    ++ (encodeUInt 1 message.sessionOptional
    ++ (encodeUInt 1 message.tradeType
    ++ (Alpha.encode message.firmId
    ++ (encodeUIntLE 2 message.oePartitionId
    ++ (encodeUIntLE 4 message.logicalAccessId
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.investorId
    ++ (Alpha.encode message.principalCode
    ++ (Alpha.encode message.clearingFirmIdOptional
    ++ (Alpha.encode message.clearingAccount
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (Alpha.encode message.freeText
    ++ (encodeUInt 1 message.settlementPeriodOptional
    ++ (encodeUInt 1 message.settlementFlagOptional
    ++ (encodeUInt 1 message.guaranteeFlagOptional))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (DcShortDeclarationFillMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (messageSendingTime, bytes) ← decodeUIntLE 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTime, bytes) ← decodeUIntLE 8 bytes
  let (oeginFromMember, bytes) ← decodeUIntLE 8 bytes
  let (oegoutTimeToMe, bytes) ← decodeUIntLE 8 bytes
  let (operationType, bytes) ← decodeUInt 1 bytes
  let (declarationEventType, bytes) ← decodeUInt 1 bytes
  let (declarationStatus, bytes) ← decodeUInt 1 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (declarationId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (crossOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (tradeTime, bytes) ← decodeUIntLE 8 bytes
  let (enteringCounterparty, bytes) ← Alpha.decode 8 bytes
  let (sessionOptional, bytes) ← decodeUInt 1 bytes
  let (tradeType, bytes) ← decodeUInt 1 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (oePartitionId, bytes) ← decodeUIntLE 2 bytes
  let (logicalAccessId, bytes) ← decodeUIntLE 4 bytes
  let (traderId, bytes) ← Alpha.decode 16 bytes
  let (investorId, bytes) ← Alpha.decode 16 bytes
  let (principalCode, bytes) ← Alpha.decode 8 bytes
  let (clearingFirmIdOptional, bytes) ← Alpha.decode 8 bytes
  let (clearingAccount, bytes) ← Alpha.decode 16 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (freeText, bytes) ← Alpha.decode 18 bytes
  let (settlementPeriodOptional, bytes) ← decodeUInt 1 bytes
  let (settlementFlagOptional, bytes) ← decodeUInt 1 bytes
  let (guaranteeFlagOptional, bytes) ← decodeUInt 1 bytes
  pure ({ msgSeqNum, produceTime, consumeTime, messageSendingTime, bookIn, bookOutTime, oeginFromMember, oegoutTimeToMe, operationType, declarationEventType, declarationStatus, eventId, emm, symbolIndex, declarationId, price, quantity, side, crossOrderIndicator, tradeTime, enteringCounterparty, sessionOptional, tradeType, firmId, oePartitionId, logicalAccessId, traderId, investorId, principalCode, clearingFirmIdOptional, clearingAccount, accountType, clientOrderId, freeText, settlementPeriodOptional, settlementFlagOptional, guaranteeFlagOptional }, bytes)

@[simp] theorem encode_length (message : DcShortDeclarationFillMessage) : (encode message).length = 228 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DcShortDeclarationFillMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : DcShortDeclarationFillMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DcShortDeclarationFillMessage

/-- D C Quote Request Message Non Modifiable Short Codes Group: 16 bytes -/
structure DCQuoteRequestMessageNonModifiableShortCodesGroup where
  originalClientIdShortCode : BitVec 32
  originalExecWFirmShortCode : BitVec 32
  originalInvestDecisWFirmShortCode : BitVec 32
  originalNonExecBrokerShortCode : BitVec 32
  deriving DecidableEq, Repr

namespace DCQuoteRequestMessageNonModifiableShortCodesGroup

def encode (message : DCQuoteRequestMessageNonModifiableShortCodesGroup) : List UInt8 :=
  encodeUIntLE 4 message.originalClientIdShortCode
    ++ (encodeUIntLE 4 message.originalExecWFirmShortCode
    ++ (encodeUIntLE 4 message.originalInvestDecisWFirmShortCode
    ++ (encodeUIntLE 4 message.originalNonExecBrokerShortCode)))

def decode (bytes : List UInt8) : Option (DCQuoteRequestMessageNonModifiableShortCodesGroup × List UInt8) := do
  let (originalClientIdShortCode, bytes) ← decodeUIntLE 4 bytes
  let (originalExecWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (originalInvestDecisWFirmShortCode, bytes) ← decodeUIntLE 4 bytes
  let (originalNonExecBrokerShortCode, bytes) ← decodeUIntLE 4 bytes
  pure ({ originalClientIdShortCode, originalExecWFirmShortCode, originalInvestDecisWFirmShortCode, originalNonExecBrokerShortCode }, bytes)

@[simp] theorem encode_length (message : DCQuoteRequestMessageNonModifiableShortCodesGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DCQuoteRequestMessageNonModifiableShortCodesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCQuoteRequestMessageNonModifiableShortCodesGroup) (rest : List UInt8) :
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

end DCQuoteRequestMessageNonModifiableShortCodesGroup

/-- D C Quote Request Message Non Modifiable Short Codes Groups -/
structure DCQuoteRequestMessageNonModifiableShortCodesGroups where
  blockLengthShort : BitVec 8
  dCQuoteRequestMessageNonModifiableShortCodesGroup : Bounded 1 DCQuoteRequestMessageNonModifiableShortCodesGroup
  deriving DecidableEq, Repr

namespace DCQuoteRequestMessageNonModifiableShortCodesGroups

def encode (message : DCQuoteRequestMessageNonModifiableShortCodesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCQuoteRequestMessageNonModifiableShortCodesGroup.val.length)
    ++ (encodeMany DCQuoteRequestMessageNonModifiableShortCodesGroup.encode message.dCQuoteRequestMessageNonModifiableShortCodesGroup.val))

def decode (bytes : List UInt8) : Option (DCQuoteRequestMessageNonModifiableShortCodesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCQuoteRequestMessageNonModifiableShortCodesGroup_, bytes) ← decodeMany DCQuoteRequestMessageNonModifiableShortCodesGroup.decode numInGroup.toNat bytes
  if fits_dCQuoteRequestMessageNonModifiableShortCodesGroup : dCQuoteRequestMessageNonModifiableShortCodesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCQuoteRequestMessageNonModifiableShortCodesGroup := ⟨dCQuoteRequestMessageNonModifiableShortCodesGroup_, fits_dCQuoteRequestMessageNonModifiableShortCodesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCQuoteRequestMessageNonModifiableShortCodesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCQuoteRequestMessageNonModifiableShortCodesGroups) : (encode message).length ≤ 4082 := by
  have bound_dCQuoteRequestMessageNonModifiableShortCodesGroup := message.dCQuoteRequestMessageNonModifiableShortCodesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCQuoteRequestMessageNonModifiableShortCodesGroup.encode 16 DCQuoteRequestMessageNonModifiableShortCodesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCQuoteRequestMessageNonModifiableShortCodesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCQuoteRequestMessageNonModifiableShortCodesGroup.encode DCQuoteRequestMessageNonModifiableShortCodesGroup.decode DCQuoteRequestMessageNonModifiableShortCodesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCQuoteRequestMessageNonModifiableShortCodesGroup.length_lt]
  rfl

end DCQuoteRequestMessageNonModifiableShortCodesGroups

/-- D C Quote Request Message Short Codes Details Non Modifiable Group: 3 bytes -/
structure DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup where
  originalShortCodeType : BitVec 8
  shortCodeRole : BitVec 8
  shortCodeRoleQualifier : BitVec 8
  deriving DecidableEq, Repr

namespace DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup

def encode (message : DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup) : List UInt8 :=
  encodeUInt 1 message.originalShortCodeType
    ++ (encodeUInt 1 message.shortCodeRole
    ++ (encodeUInt 1 message.shortCodeRoleQualifier))

def decode (bytes : List UInt8) : Option (DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup × List UInt8) := do
  let (originalShortCodeType, bytes) ← decodeUInt 1 bytes
  let (shortCodeRole, bytes) ← decodeUInt 1 bytes
  let (shortCodeRoleQualifier, bytes) ← decodeUInt 1 bytes
  pure ({ originalShortCodeType, shortCodeRole, shortCodeRoleQualifier }, bytes)

@[simp] theorem encode_length (message : DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup

/-- D C Quote Request Message Short Codes Details Non Modifiable Groups -/
structure DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups where
  blockLengthShort : BitVec 8
  dCQuoteRequestMessageShortCodesDetailsNonModifiableGroup : Bounded 1 DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup
  deriving DecidableEq, Repr

namespace DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups

def encode (message : DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCQuoteRequestMessageShortCodesDetailsNonModifiableGroup.val.length)
    ++ (encodeMany DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup.encode message.dCQuoteRequestMessageShortCodesDetailsNonModifiableGroup.val))

def decode (bytes : List UInt8) : Option (DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCQuoteRequestMessageShortCodesDetailsNonModifiableGroup_, bytes) ← decodeMany DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup.decode numInGroup.toNat bytes
  if fits_dCQuoteRequestMessageShortCodesDetailsNonModifiableGroup : dCQuoteRequestMessageShortCodesDetailsNonModifiableGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCQuoteRequestMessageShortCodesDetailsNonModifiableGroup := ⟨dCQuoteRequestMessageShortCodesDetailsNonModifiableGroup_, fits_dCQuoteRequestMessageShortCodesDetailsNonModifiableGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups) : (encode message).length ≤ 767 := by
  have bound_dCQuoteRequestMessageShortCodesDetailsNonModifiableGroup := message.dCQuoteRequestMessageShortCodesDetailsNonModifiableGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup.encode 3 DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup.encode DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup.decode DCQuoteRequestMessageShortCodesDetailsNonModifiableGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCQuoteRequestMessageShortCodesDetailsNonModifiableGroup.length_lt]
  rfl

end DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups

/-- D C Quote Request Message Rf Q Optional Fields Group: 11 bytes -/
structure DCQuoteRequestMessageRfQOptionalFieldsGroup where
  limitMatchingPrice : BitVec 64
  minimumNumberOfLPs : BitVec 8
  expirationDelay : BitVec 16
  deriving DecidableEq, Repr

namespace DCQuoteRequestMessageRfQOptionalFieldsGroup

def encode (message : DCQuoteRequestMessageRfQOptionalFieldsGroup) : List UInt8 :=
  encodeUIntLE 8 message.limitMatchingPrice
    ++ (encodeUInt 1 message.minimumNumberOfLPs
    ++ (encodeUIntLE 2 message.expirationDelay))

def decode (bytes : List UInt8) : Option (DCQuoteRequestMessageRfQOptionalFieldsGroup × List UInt8) := do
  let (limitMatchingPrice, bytes) ← decodeUIntLE 8 bytes
  let (minimumNumberOfLPs, bytes) ← decodeUInt 1 bytes
  let (expirationDelay, bytes) ← decodeUIntLE 2 bytes
  pure ({ limitMatchingPrice, minimumNumberOfLPs, expirationDelay }, bytes)

@[simp] theorem encode_length (message : DCQuoteRequestMessageRfQOptionalFieldsGroup) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DCQuoteRequestMessageRfQOptionalFieldsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DCQuoteRequestMessageRfQOptionalFieldsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DCQuoteRequestMessageRfQOptionalFieldsGroup

/-- D C Quote Request Message Rf Q Optional Fields Groups -/
structure DCQuoteRequestMessageRfQOptionalFieldsGroups where
  blockLengthShort : BitVec 8
  dCQuoteRequestMessageRfQOptionalFieldsGroup : Bounded 1 DCQuoteRequestMessageRfQOptionalFieldsGroup
  deriving DecidableEq, Repr

namespace DCQuoteRequestMessageRfQOptionalFieldsGroups

def encode (message : DCQuoteRequestMessageRfQOptionalFieldsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.dCQuoteRequestMessageRfQOptionalFieldsGroup.val.length)
    ++ (encodeMany DCQuoteRequestMessageRfQOptionalFieldsGroup.encode message.dCQuoteRequestMessageRfQOptionalFieldsGroup.val))

def decode (bytes : List UInt8) : Option (DCQuoteRequestMessageRfQOptionalFieldsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (dCQuoteRequestMessageRfQOptionalFieldsGroup_, bytes) ← decodeMany DCQuoteRequestMessageRfQOptionalFieldsGroup.decode numInGroup.toNat bytes
  if fits_dCQuoteRequestMessageRfQOptionalFieldsGroup : dCQuoteRequestMessageRfQOptionalFieldsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, dCQuoteRequestMessageRfQOptionalFieldsGroup := ⟨dCQuoteRequestMessageRfQOptionalFieldsGroup_, fits_dCQuoteRequestMessageRfQOptionalFieldsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DCQuoteRequestMessageRfQOptionalFieldsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DCQuoteRequestMessageRfQOptionalFieldsGroups) : (encode message).length ≤ 2807 := by
  have bound_dCQuoteRequestMessageRfQOptionalFieldsGroup := message.dCQuoteRequestMessageRfQOptionalFieldsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const DCQuoteRequestMessageRfQOptionalFieldsGroup.encode 11 DCQuoteRequestMessageRfQOptionalFieldsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DCQuoteRequestMessageRfQOptionalFieldsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DCQuoteRequestMessageRfQOptionalFieldsGroup.encode DCQuoteRequestMessageRfQOptionalFieldsGroup.decode DCQuoteRequestMessageRfQOptionalFieldsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dCQuoteRequestMessageRfQOptionalFieldsGroup.length_lt]
  rfl

end DCQuoteRequestMessageRfQOptionalFieldsGroups

/-- Dc Quote Request Message -/
structure DcQuoteRequestMessage where
  msgSeqNum : BitVec 32
  produceTime : BitVec 64
  consumeTime : BitVec 64
  eventId : BitVec 64
  bookIn : BitVec 64
  bookOutTime : BitVec 64
  clientOrderId : BitVec 64
  darkExecutionInstruction : BitVec 8
  emm : BitVec 8
  endClient : Alpha 11
  firmId : Alpha 8
  firmIdPublication : BitVec 8
  oeSessionId : BitVec 64
  oeginFromMember : BitVec 64
  oegoutTimeToMe : BitVec 64
  orderId : BitVec 64
  orderQty : BitVec 64
  orderSideOptional : BitVec 8
  rfqStatus : BitVec 8
  symbolIndex : BitVec 32
  minOrderQty : BitVec 64
  sequenceTime : BitVec 64
  rfqType : BitVec 8
  dCQuoteRequestMessageNonModifiableShortCodesGroups : DCQuoteRequestMessageNonModifiableShortCodesGroups
  dCQuoteRequestMessageShortCodesDetailsNonModifiableGroups : DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups
  dCQuoteRequestMessageRfQOptionalFieldsGroups : DCQuoteRequestMessageRfQOptionalFieldsGroups
  deriving DecidableEq, Repr

namespace DcQuoteRequestMessage

def encode (message : DcQuoteRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUIntLE 8 message.bookIn
    ++ (encodeUIntLE 8 message.bookOutTime
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 1 message.darkExecutionInstruction
    ++ (encodeUInt 1 message.emm
    ++ (Alpha.encode message.endClient
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 1 message.firmIdPublication
    ++ (encodeUIntLE 8 message.oeSessionId
    ++ (encodeUIntLE 8 message.oeginFromMember
    ++ (encodeUIntLE 8 message.oegoutTimeToMe
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUInt 1 message.orderSideOptional
    ++ (encodeUInt 1 message.rfqStatus
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.minOrderQty
    ++ (encodeUIntLE 8 message.sequenceTime
    ++ (encodeUInt 1 message.rfqType
    ++ (DCQuoteRequestMessageNonModifiableShortCodesGroups.encode message.dCQuoteRequestMessageNonModifiableShortCodesGroups
    ++ (DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups.encode message.dCQuoteRequestMessageShortCodesDetailsNonModifiableGroups
    ++ (DCQuoteRequestMessageRfQOptionalFieldsGroups.encode message.dCQuoteRequestMessageRfQOptionalFieldsGroups)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (DcQuoteRequestMessage × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (bookIn, bytes) ← decodeUIntLE 8 bytes
  let (bookOutTime, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (darkExecutionInstruction, bytes) ← decodeUIntLE 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (endClient, bytes) ← Alpha.decode 11 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (firmIdPublication, bytes) ← decodeUInt 1 bytes
  let (oeSessionId, bytes) ← decodeUIntLE 8 bytes
  let (oeginFromMember, bytes) ← decodeUIntLE 8 bytes
  let (oegoutTimeToMe, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (orderSideOptional, bytes) ← decodeUInt 1 bytes
  let (rfqStatus, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (minOrderQty, bytes) ← decodeUIntLE 8 bytes
  let (sequenceTime, bytes) ← decodeUIntLE 8 bytes
  let (rfqType, bytes) ← decodeUInt 1 bytes
  let (dCQuoteRequestMessageNonModifiableShortCodesGroups, bytes) ← DCQuoteRequestMessageNonModifiableShortCodesGroups.decode bytes
  let (dCQuoteRequestMessageShortCodesDetailsNonModifiableGroups, bytes) ← DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups.decode bytes
  let (dCQuoteRequestMessageRfQOptionalFieldsGroups, bytes) ← DCQuoteRequestMessageRfQOptionalFieldsGroups.decode bytes
  pure ({ msgSeqNum, produceTime, consumeTime, eventId, bookIn, bookOutTime, clientOrderId, darkExecutionInstruction, emm, endClient, firmId, firmIdPublication, oeSessionId, oeginFromMember, oegoutTimeToMe, orderId, orderQty, orderSideOptional, rfqStatus, symbolIndex, minOrderQty, sequenceTime, rfqType, dCQuoteRequestMessageNonModifiableShortCodesGroups, dCQuoteRequestMessageShortCodesDetailsNonModifiableGroups, dCQuoteRequestMessageRfQOptionalFieldsGroups }, bytes)

theorem encode_length_pos (message : DcQuoteRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DcQuoteRequestMessage) : (encode message).length ≤ 7793 := by
  have bound_dCQuoteRequestMessageNonModifiableShortCodesGroups := DCQuoteRequestMessageNonModifiableShortCodesGroups.encode_length_le message.dCQuoteRequestMessageNonModifiableShortCodesGroups
  have bound_dCQuoteRequestMessageShortCodesDetailsNonModifiableGroups := DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups.encode_length_le message.dCQuoteRequestMessageShortCodesDetailsNonModifiableGroups
  have bound_dCQuoteRequestMessageRfQOptionalFieldsGroups := DCQuoteRequestMessageRfQOptionalFieldsGroups.encode_length_le message.dCQuoteRequestMessageRfQOptionalFieldsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : DcQuoteRequestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, DCQuoteRequestMessageNonModifiableShortCodesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DCQuoteRequestMessageShortCodesDetailsNonModifiableGroups.decode_encode, some_bind]
  dsimp only
  rw [DCQuoteRequestMessageRfQOptionalFieldsGroups.decode_encode, some_bind]
  rfl

end DcQuoteRequestMessage

/-- Dc Clear Book Message: 38 bytes -/
structure DcClearBookMessage where
  produceTime : BitVec 64
  consumeTime : BitVec 64
  sequenceTime : BitVec 64
  bookInTime : BitVec 64
  symbolIndex : BitVec 32
  emm : BitVec 8
  clearBookOrigin : BitVec 8
  deriving DecidableEq, Repr

namespace DcClearBookMessage

def encode (message : DcClearBookMessage) : List UInt8 :=
  encodeUIntLE 8 message.produceTime
    ++ (encodeUIntLE 8 message.consumeTime
    ++ (encodeUIntLE 8 message.sequenceTime
    ++ (encodeUIntLE 8 message.bookInTime
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.emm
    ++ (encodeUInt 1 message.clearBookOrigin))))))

def decode (bytes : List UInt8) : Option (DcClearBookMessage × List UInt8) := do
  let (produceTime, bytes) ← decodeUIntLE 8 bytes
  let (consumeTime, bytes) ← decodeUIntLE 8 bytes
  let (sequenceTime, bytes) ← decodeUIntLE 8 bytes
  let (bookInTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (clearBookOrigin, bytes) ← decodeUInt 1 bytes
  pure ({ produceTime, consumeTime, sequenceTime, bookInTime, symbolIndex, emm, clearBookOrigin }, bytes)

@[simp] theorem encode_length (message : DcClearBookMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DcClearBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcClearBookMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DcClearBookMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | dcMarketStatusChangeMessage (message : DcMarketStatusChangeMessage) -- 16001
  | dcPriceUpdateMessage (message : DcPriceUpdateMessage) -- 16003
  | longOrderMessage (message : LongOrderMessage) -- 16006
  | dcShortOrderRejectMessage (message : DcShortOrderRejectMessage) -- 16010
  | dcShortTradeCancellationMessage (message : DcShortTradeCancellationMessage) -- 16016
  | dcStaticCollarsMessage (message : DcStaticCollarsMessage) -- 16018
  | tradeBustNotificationMessage (message : TradeBustNotificationMessage) -- 16021
  | dcQuoteMessage (message : DcQuoteMessage) -- 16050
  | dcafqrfeMessage (message : DcafqrfeMessage) -- 16051
  | dcDeclarationNewMessage (message : DcDeclarationNewMessage) -- 16052
  | dcShortDeclarationRejectMessage (message : DcShortDeclarationRejectMessage) -- 16053
  | dcShortDeclarationCancelMessage (message : DcShortDeclarationCancelMessage) -- 16054
  | dcShortTradeDeclarationMessage (message : DcShortTradeDeclarationMessage) -- 16055
  | dcShortTradeDeclarationCancellationMessage (message : DcShortTradeDeclarationCancellationMessage) -- 16056
  | dcTradeBustDeclarationMessage (message : DcTradeBustDeclarationMessage) -- 16057
  | dcTradeMessage (message : DcTradeMessage) -- 16058
  | dcShortDeclarationFillMessage (message : DcShortDeclarationFillMessage) -- 16059
  | dcQuoteRequestMessage (message : DcQuoteRequestMessage) -- 16060
  | dcClearBookMessage (message : DcClearBookMessage) -- 16061
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .dcMarketStatusChangeMessage _ => 16001
  | .dcPriceUpdateMessage _ => 16003
  | .longOrderMessage _ => 16006
  | .dcShortOrderRejectMessage _ => 16010
  | .dcShortTradeCancellationMessage _ => 16016
  | .dcStaticCollarsMessage _ => 16018
  | .tradeBustNotificationMessage _ => 16021
  | .dcQuoteMessage _ => 16050
  | .dcafqrfeMessage _ => 16051
  | .dcDeclarationNewMessage _ => 16052
  | .dcShortDeclarationRejectMessage _ => 16053
  | .dcShortDeclarationCancelMessage _ => 16054
  | .dcShortTradeDeclarationMessage _ => 16055
  | .dcShortTradeDeclarationCancellationMessage _ => 16056
  | .dcTradeBustDeclarationMessage _ => 16057
  | .dcTradeMessage _ => 16058
  | .dcShortDeclarationFillMessage _ => 16059
  | .dcQuoteRequestMessage _ => 16060
  | .dcClearBookMessage _ => 16061

def encode : Payload → List UInt8
  | .dcMarketStatusChangeMessage message => DcMarketStatusChangeMessage.encode message
  | .dcPriceUpdateMessage message => DcPriceUpdateMessage.encode message
  | .longOrderMessage message => LongOrderMessage.encode message
  | .dcShortOrderRejectMessage message => DcShortOrderRejectMessage.encode message
  | .dcShortTradeCancellationMessage message => DcShortTradeCancellationMessage.encode message
  | .dcStaticCollarsMessage message => DcStaticCollarsMessage.encode message
  | .tradeBustNotificationMessage message => TradeBustNotificationMessage.encode message
  | .dcQuoteMessage message => DcQuoteMessage.encode message
  | .dcafqrfeMessage message => DcafqrfeMessage.encode message
  | .dcDeclarationNewMessage message => DcDeclarationNewMessage.encode message
  | .dcShortDeclarationRejectMessage message => DcShortDeclarationRejectMessage.encode message
  | .dcShortDeclarationCancelMessage message => DcShortDeclarationCancelMessage.encode message
  | .dcShortTradeDeclarationMessage message => DcShortTradeDeclarationMessage.encode message
  | .dcShortTradeDeclarationCancellationMessage message => DcShortTradeDeclarationCancellationMessage.encode message
  | .dcTradeBustDeclarationMessage message => DcTradeBustDeclarationMessage.encode message
  | .dcTradeMessage message => DcTradeMessage.encode message
  | .dcShortDeclarationFillMessage message => DcShortDeclarationFillMessage.encode message
  | .dcQuoteRequestMessage message => DcQuoteRequestMessage.encode message
  | .dcClearBookMessage message => DcClearBookMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 73740 := by
  cases message with
  | dcMarketStatusChangeMessage inner =>
    simp only [encode, DcMarketStatusChangeMessage.encode_length]
    omega
  | dcPriceUpdateMessage inner =>
    simp only [encode, DcPriceUpdateMessage.encode_length]
    omega
  | longOrderMessage inner =>
    have bound_inner := LongOrderMessage.encode_length_le inner
    simp only [encode]
    omega
  | dcShortOrderRejectMessage inner =>
    have bound_inner := DcShortOrderRejectMessage.encode_length_le inner
    simp only [encode]
    omega
  | dcShortTradeCancellationMessage inner =>
    simp only [encode, DcShortTradeCancellationMessage.encode_length]
    omega
  | dcStaticCollarsMessage inner =>
    have bound_inner := DcStaticCollarsMessage.encode_length_le inner
    simp only [encode]
    omega
  | tradeBustNotificationMessage inner =>
    have bound_inner := TradeBustNotificationMessage.encode_length_le inner
    simp only [encode]
    omega
  | dcQuoteMessage inner =>
    have bound_inner := DcQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | dcafqrfeMessage inner =>
    simp only [encode, DcafqrfeMessage.encode_length]
    omega
  | dcDeclarationNewMessage inner =>
    simp only [encode, DcDeclarationNewMessage.encode_length]
    omega
  | dcShortDeclarationRejectMessage inner =>
    simp only [encode, DcShortDeclarationRejectMessage.encode_length]
    omega
  | dcShortDeclarationCancelMessage inner =>
    simp only [encode, DcShortDeclarationCancelMessage.encode_length]
    omega
  | dcShortTradeDeclarationMessage inner =>
    have bound_inner := DcShortTradeDeclarationMessage.encode_length_le inner
    simp only [encode]
    omega
  | dcShortTradeDeclarationCancellationMessage inner =>
    simp only [encode, DcShortTradeDeclarationCancellationMessage.encode_length]
    omega
  | dcTradeBustDeclarationMessage inner =>
    simp only [encode, DcTradeBustDeclarationMessage.encode_length]
    omega
  | dcTradeMessage inner =>
    have bound_inner := DcTradeMessage.encode_length_le inner
    simp only [encode]
    omega
  | dcShortDeclarationFillMessage inner =>
    simp only [encode, DcShortDeclarationFillMessage.encode_length]
    omega
  | dcQuoteRequestMessage inner =>
    have bound_inner := DcQuoteRequestMessage.encode_length_le inner
    simp only [encode]
    omega
  | dcClearBookMessage inner =>
    simp only [encode, DcClearBookMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 16001 then (DcMarketStatusChangeMessage.decode bytes).map fun (message, rest) => (.dcMarketStatusChangeMessage message, rest)
  else if tag = 16003 then (DcPriceUpdateMessage.decode bytes).map fun (message, rest) => (.dcPriceUpdateMessage message, rest)
  else if tag = 16006 then (LongOrderMessage.decode bytes).map fun (message, rest) => (.longOrderMessage message, rest)
  else if tag = 16010 then (DcShortOrderRejectMessage.decode bytes).map fun (message, rest) => (.dcShortOrderRejectMessage message, rest)
  else if tag = 16016 then (DcShortTradeCancellationMessage.decode bytes).map fun (message, rest) => (.dcShortTradeCancellationMessage message, rest)
  else if tag = 16018 then (DcStaticCollarsMessage.decode bytes).map fun (message, rest) => (.dcStaticCollarsMessage message, rest)
  else if tag = 16021 then (TradeBustNotificationMessage.decode bytes).map fun (message, rest) => (.tradeBustNotificationMessage message, rest)
  else if tag = 16050 then (DcQuoteMessage.decode bytes).map fun (message, rest) => (.dcQuoteMessage message, rest)
  else if tag = 16051 then (DcafqrfeMessage.decode bytes).map fun (message, rest) => (.dcafqrfeMessage message, rest)
  else if tag = 16052 then (DcDeclarationNewMessage.decode bytes).map fun (message, rest) => (.dcDeclarationNewMessage message, rest)
  else if tag = 16053 then (DcShortDeclarationRejectMessage.decode bytes).map fun (message, rest) => (.dcShortDeclarationRejectMessage message, rest)
  else if tag = 16054 then (DcShortDeclarationCancelMessage.decode bytes).map fun (message, rest) => (.dcShortDeclarationCancelMessage message, rest)
  else if tag = 16055 then (DcShortTradeDeclarationMessage.decode bytes).map fun (message, rest) => (.dcShortTradeDeclarationMessage message, rest)
  else if tag = 16056 then (DcShortTradeDeclarationCancellationMessage.decode bytes).map fun (message, rest) => (.dcShortTradeDeclarationCancellationMessage message, rest)
  else if tag = 16057 then (DcTradeBustDeclarationMessage.decode bytes).map fun (message, rest) => (.dcTradeBustDeclarationMessage message, rest)
  else if tag = 16058 then (DcTradeMessage.decode bytes).map fun (message, rest) => (.dcTradeMessage message, rest)
  else if tag = 16059 then (DcShortDeclarationFillMessage.decode bytes).map fun (message, rest) => (.dcShortDeclarationFillMessage message, rest)
  else if tag = 16060 then (DcQuoteRequestMessage.decode bytes).map fun (message, rest) => (.dcQuoteRequestMessage message, rest)
  else if tag = 16061 then (DcClearBookMessage.decode bytes).map fun (message, rest) => (.dcClearBookMessage message, rest)
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
theorem encode_length_le (message : Message) : (encode message).length ≤ 73750 := by
  unfold encode
  cases message.payload with
  | dcMarketStatusChangeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DcMarketStatusChangeMessage.encode_length]
    omega
  | dcPriceUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DcPriceUpdateMessage.encode_length]
    omega
  | longOrderMessage inner =>
    have bound_inner := LongOrderMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | dcShortOrderRejectMessage inner =>
    have bound_inner := DcShortOrderRejectMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | dcShortTradeCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DcShortTradeCancellationMessage.encode_length]
    omega
  | dcStaticCollarsMessage inner =>
    have bound_inner := DcStaticCollarsMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | tradeBustNotificationMessage inner =>
    have bound_inner := TradeBustNotificationMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | dcQuoteMessage inner =>
    have bound_inner := DcQuoteMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | dcafqrfeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DcafqrfeMessage.encode_length]
    omega
  | dcDeclarationNewMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DcDeclarationNewMessage.encode_length]
    omega
  | dcShortDeclarationRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DcShortDeclarationRejectMessage.encode_length]
    omega
  | dcShortDeclarationCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DcShortDeclarationCancelMessage.encode_length]
    omega
  | dcShortTradeDeclarationMessage inner =>
    have bound_inner := DcShortTradeDeclarationMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | dcShortTradeDeclarationCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DcShortTradeDeclarationCancellationMessage.encode_length]
    omega
  | dcTradeBustDeclarationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DcTradeBustDeclarationMessage.encode_length]
    omega
  | dcTradeMessage inner =>
    have bound_inner := DcTradeMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | dcShortDeclarationFillMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DcShortDeclarationFillMessage.encode_length]
    omega
  | dcQuoteRequestMessage inner =>
    have bound_inner := DcQuoteRequestMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | dcClearBookMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, DcClearBookMessage.encode_length]
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

end Omi.EuronextOptiqDropcopygatewaySbeV669
