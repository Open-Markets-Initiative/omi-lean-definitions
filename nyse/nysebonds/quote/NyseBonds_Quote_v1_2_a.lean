import Wire

/-!
# New York Stock Exchange Quote v1.2.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseNysebondsQuotePdpV12A

/-- Exchange Id: one byte code -/
def ExchangeId.codes : List UInt8 :=
  [0x4E, 0x50]

inductive ExchangeId where
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeId

def toByte : ExchangeId → UInt8
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExchangeId :=
  if byte = 0x4E then .nyse
  else .nyseArca

def ofByte (byte : UInt8) : ExchangeId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeId) : ofByte value.toByte = value := by
  cases value with
  | nyse => decide
  | nyseArca => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExchangeId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExchangeId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExchangeId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExchangeId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExchangeId

/-- Security Type: one byte code -/
def SecurityType.codes : List UInt8 :=
  [0x46]

inductive SecurityType where
  | fixedIncomeBonds -- Fixed Income Bonds
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityType

def toByte : SecurityType → UInt8
  | .fixedIncomeBonds => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : SecurityType :=
  .fixedIncomeBonds

def ofByte (byte : UInt8) : SecurityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityType) : ofByte value.toByte = value := by
  cases value with
  | fixedIncomeBonds => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityType

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x45, 0x46, 0x48, 0x4E, 0x4F, 0x52, 0x55, 0x57]

inductive QuoteCondition where
  | slowOnAskSide -- Slow On Ask Side
  | slowOnBidSide -- Slow On Bid Side
  | closing -- Closing
  | slowOnTheBidDueToAnLrpOrGapQuote -- Slow On The Bid Due To An Lrp Or Gap Quote
  | slowOnTheAskDueToAnLrpOrGapQuote -- Slow On The Ask Due To An Lrp Or Gap Quote
  | slowOnBothAskAndBid -- Slow On Both Ask And Bid
  | nonfirmQuote -- Nonfirm Quote
  | openingQuote -- Opening Quote
  | regularQuote -- Regular Quote
  | slowOnTheBidAndAskDueToAnLrpOrGapQuote -- Slow On The Bid And Ask Due To An Lrp Or Gap Quote
  | slowOnTheBidAndAskDueToASetSlowList -- Slow On The Bid And Ask Due To A Set Slow List
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .slowOnAskSide => 0x41
  | .slowOnBidSide => 0x42
  | .closing => 0x43
  | .slowOnTheBidDueToAnLrpOrGapQuote => 0x45
  | .slowOnTheAskDueToAnLrpOrGapQuote => 0x46
  | .slowOnBothAskAndBid => 0x48
  | .nonfirmQuote => 0x4E
  | .openingQuote => 0x4F
  | .regularQuote => 0x52
  | .slowOnTheBidAndAskDueToAnLrpOrGapQuote => 0x55
  | .slowOnTheBidAndAskDueToASetSlowList => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x41 then .slowOnAskSide
  else if byte = 0x42 then .slowOnBidSide
  else if byte = 0x43 then .closing
  else if byte = 0x45 then .slowOnTheBidDueToAnLrpOrGapQuote
  else if byte = 0x46 then .slowOnTheAskDueToAnLrpOrGapQuote
  else if byte = 0x48 then .slowOnBothAskAndBid
  else if byte = 0x4E then .nonfirmQuote
  else if byte = 0x4F then .openingQuote
  else if byte = 0x52 then .regularQuote
  else if byte = 0x55 then .slowOnTheBidAndAskDueToAnLrpOrGapQuote
  else .slowOnTheBidAndAskDueToASetSlowList

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | slowOnAskSide => decide
  | slowOnBidSide => decide
  | closing => decide
  | slowOnTheBidDueToAnLrpOrGapQuote => decide
  | slowOnTheAskDueToAnLrpOrGapQuote => decide
  | slowOnBothAskAndBid => decide
  | nonfirmQuote => decide
  | openingQuote => decide
  | regularQuote => decide
  | slowOnTheBidAndAskDueToAnLrpOrGapQuote => decide
  | slowOnTheBidAndAskDueToASetSlowList => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : QuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteCondition

/-- Flat Pricing: one byte code -/
def FlatPricing.codes : List UInt8 :=
  [0x46]

inductive FlatPricing where
  | flatPricingIsInEffect -- Flat Pricing Is In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ FlatPricing.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FlatPricing

def toByte : FlatPricing → UInt8
  | .flatPricingIsInEffect => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : FlatPricing :=
  .flatPricingIsInEffect

def ofByte (byte : UInt8) : FlatPricing :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FlatPricing) : ofByte value.toByte = value := by
  cases value with
  | flatPricingIsInEffect => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FlatPricing) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FlatPricing × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FlatPricing) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FlatPricing) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FlatPricing

/-- Sequence Number Reset Message: 4 bytes -/
structure SequenceNumberResetMessage where
  nextSeqNumber : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceNumberResetMessage

def encode (message : SequenceNumberResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.nextSeqNumber

def decode (bytes : List UInt8) : Option (SequenceNumberResetMessage × List UInt8) := do
  let (nextSeqNumber, bytes) ← decodeUIntLE 4 bytes
  pure ({ nextSeqNumber }, bytes)

@[simp] theorem encode_length (message : SequenceNumberResetMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceNumberResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceNumberResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceNumberResetMessage

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

/-- Message Unavailable Message: 8 bytes -/
structure MessageUnavailableMessage where
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace MessageUnavailableMessage

def encode (message : MessageUnavailableMessage) : List UInt8 :=
  encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum)

def decode (bytes : List UInt8) : Option (MessageUnavailableMessage × List UInt8) := do
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ beginSeqNum, endSeqNum }, bytes)

@[simp] theorem encode_length (message : MessageUnavailableMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MessageUnavailableMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageUnavailableMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MessageUnavailableMessage

/-- Refresh Quote Message: 72 bytes -/
structure RefreshQuoteMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  quoteLinkId : BitVec 32
  askPriceNumerator : BitVec 32
  askSize : BitVec 32
  bidPriceNumerator : BitVec 32
  bidSize : BitVec 32
  priceScaleCode : BitVec 8
  exchangeId : ExchangeId
  securityType : SecurityType
  quoteCondition : QuoteCondition
  flatPricing : FlatPricing
  tradingAction : BitVec 8
  fillerAscii2 : Alpha 2
  symbol : Alpha 22
  cusip : Alpha 14
  deriving DecidableEq, Repr

namespace RefreshQuoteMessage

def encode (message : RefreshQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.quoteLinkId
    ++ (encodeUIntLE 4 message.askPriceNumerator
    ++ (encodeUIntLE 4 message.askSize
    ++ (encodeUIntLE 4 message.bidPriceNumerator
    ++ (encodeUIntLE 4 message.bidSize
    ++ (encodeUIntLE 1 message.priceScaleCode
    ++ (ExchangeId.encode message.exchangeId
    ++ (SecurityType.encode message.securityType
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (FlatPricing.encode message.flatPricing
    ++ (encodeUIntLE 1 message.tradingAction
    ++ (Alpha.encode message.fillerAscii2
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.cusip)))))))))))))))

def decode (bytes : List UInt8) : Option (RefreshQuoteMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (quoteLinkId, bytes) ← decodeUIntLE 4 bytes
  let (askPriceNumerator, bytes) ← decodeUIntLE 4 bytes
  let (askSize, bytes) ← decodeUIntLE 4 bytes
  let (bidPriceNumerator, bytes) ← decodeUIntLE 4 bytes
  let (bidSize, bytes) ← decodeUIntLE 4 bytes
  let (priceScaleCode, bytes) ← decodeUIntLE 1 bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (securityType, bytes) ← SecurityType.decode bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (flatPricing, bytes) ← FlatPricing.decode bytes
  let (tradingAction, bytes) ← decodeUIntLE 1 bytes
  let (fillerAscii2, bytes) ← Alpha.decode 2 bytes
  let (symbol, bytes) ← Alpha.decode 22 bytes
  let (cusip, bytes) ← Alpha.decode 14 bytes
  pure ({ symbolIndex, sourceTime, quoteLinkId, askPriceNumerator, askSize, bidPriceNumerator, bidSize, priceScaleCode, exchangeId, securityType, quoteCondition, flatPricing, tradingAction, fillerAscii2, symbol, cusip }, bytes)

@[simp] theorem encode_length (message : RefreshQuoteMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ExchangeId.encode_length, SecurityType.encode_length, QuoteCondition.encode_length, FlatPricing.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RefreshQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FlatPricing.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefreshQuoteMessage

/-- Symbol Index Mapping Message: 44 bytes -/
structure SymbolIndexMappingMessage where
  symbolIndex : BitVec 32
  symbol : Alpha 22
  cusip : Alpha 14
  fillerAscii4 : Alpha 4
  deriving DecidableEq, Repr

namespace SymbolIndexMappingMessage

def encode (message : SymbolIndexMappingMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.cusip
    ++ (Alpha.encode message.fillerAscii4)))

def decode (bytes : List UInt8) : Option (SymbolIndexMappingMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 22 bytes
  let (cusip, bytes) ← Alpha.decode 14 bytes
  let (fillerAscii4, bytes) ← Alpha.decode 4 bytes
  pure ({ symbolIndex, symbol, cusip, fillerAscii4 }, bytes)

@[simp] theorem encode_length (message : SymbolIndexMappingMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SymbolIndexMappingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolIndexMappingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolIndexMappingMessage

/-- Quote Message: 36 bytes -/
structure QuoteMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  quoteLinkId : BitVec 32
  askPriceNumerator : BitVec 32
  askSize : BitVec 32
  bidPriceNumerator : BitVec 32
  bidSize : BitVec 32
  priceScaleCode : BitVec 8
  exchangeId : ExchangeId
  securityType : SecurityType
  quoteCondition : QuoteCondition
  flatPricing : FlatPricing
  tradingAction : BitVec 8
  fillerAscii2 : Alpha 2
  deriving DecidableEq, Repr

namespace QuoteMessage

def encode (message : QuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.quoteLinkId
    ++ (encodeUIntLE 4 message.askPriceNumerator
    ++ (encodeUIntLE 4 message.askSize
    ++ (encodeUIntLE 4 message.bidPriceNumerator
    ++ (encodeUIntLE 4 message.bidSize
    ++ (encodeUIntLE 1 message.priceScaleCode
    ++ (ExchangeId.encode message.exchangeId
    ++ (SecurityType.encode message.securityType
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (FlatPricing.encode message.flatPricing
    ++ (encodeUIntLE 1 message.tradingAction
    ++ (Alpha.encode message.fillerAscii2)))))))))))))

def decode (bytes : List UInt8) : Option (QuoteMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (quoteLinkId, bytes) ← decodeUIntLE 4 bytes
  let (askPriceNumerator, bytes) ← decodeUIntLE 4 bytes
  let (askSize, bytes) ← decodeUIntLE 4 bytes
  let (bidPriceNumerator, bytes) ← decodeUIntLE 4 bytes
  let (bidSize, bytes) ← decodeUIntLE 4 bytes
  let (priceScaleCode, bytes) ← decodeUIntLE 1 bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (securityType, bytes) ← SecurityType.decode bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (flatPricing, bytes) ← FlatPricing.decode bytes
  let (tradingAction, bytes) ← decodeUIntLE 1 bytes
  let (fillerAscii2, bytes) ← Alpha.decode 2 bytes
  pure ({ symbolIndex, sourceTime, quoteLinkId, askPriceNumerator, askSize, bidPriceNumerator, bidSize, priceScaleCode, exchangeId, securityType, quoteCondition, flatPricing, tradingAction, fillerAscii2 }, bytes)

@[simp] theorem encode_length (message : QuoteMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ExchangeId.encode_length, SecurityType.encode_length, QuoteCondition.encode_length, FlatPricing.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FlatPricing.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | sequenceNumberResetMessage (message : SequenceNumberResetMessage) -- 1
  | heartbeatMessage (message : HeartbeatMessage) -- 2
  | messageUnavailableMessage (message : MessageUnavailableMessage) -- 5
  | refreshQuoteMessage (message : RefreshQuoteMessage) -- 23
  | symbolIndexMappingMessage (message : SymbolIndexMappingMessage) -- 26
  | quoteMessage (message : QuoteMessage) -- 141
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceNumberResetMessage _ => 1
  | .heartbeatMessage _ => 2
  | .messageUnavailableMessage _ => 5
  | .refreshQuoteMessage _ => 23
  | .symbolIndexMappingMessage _ => 26
  | .quoteMessage _ => 141

def encode : Payload → List UInt8
  | .sequenceNumberResetMessage message => SequenceNumberResetMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .messageUnavailableMessage message => MessageUnavailableMessage.encode message
  | .refreshQuoteMessage message => RefreshQuoteMessage.encode message
  | .symbolIndexMappingMessage message => SymbolIndexMappingMessage.encode message
  | .quoteMessage message => QuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 72 := by
  cases message with
  | sequenceNumberResetMessage inner =>
    simp only [encode, SequenceNumberResetMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | messageUnavailableMessage inner =>
    simp only [encode, MessageUnavailableMessage.encode_length]
    omega
  | refreshQuoteMessage inner =>
    simp only [encode, RefreshQuoteMessage.encode_length]
    omega
  | symbolIndexMappingMessage inner =>
    simp only [encode, SymbolIndexMappingMessage.encode_length]
    omega
  | quoteMessage inner =>
    simp only [encode, QuoteMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (SequenceNumberResetMessage.decode bytes).map fun (message, rest) => (.sequenceNumberResetMessage message, rest)
  else if tag = 2 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 5 then (MessageUnavailableMessage.decode bytes).map fun (message, rest) => (.messageUnavailableMessage message, rest)
  else if tag = 23 then (RefreshQuoteMessage.decode bytes).map fun (message, rest) => (.refreshQuoteMessage message, rest)
  else if tag = 26 then (SymbolIndexMappingMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingMessage message, rest)
  else if tag = 141 then (QuoteMessage.decode bytes).map fun (message, rest) => (.quoteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  msgSeqNum : BitVec 32
  sendTime : BitVec 32
  productId : BitVec 8
  retransFlag : BitVec 8
  numBodyEntries : BitVec 8
  filler : Alpha 1
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 2 (Payload.tag message.payload)
    ++ (encodeUInt 4 message.msgSeqNum
    ++ (encodeUInt 4 message.sendTime
    ++ (encodeUInt 1 message.productId
    ++ (encodeUInt 1 message.retransFlag
    ++ (encodeUInt 1 message.numBodyEntries
    ++ (Alpha.encode message.filler
    ++ (Payload.encode message.payload)))))))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 2 bytes
  let (msgSeqNum, bytes) ← decodeUInt 4 bytes
  let (sendTime, bytes) ← decodeUInt 4 bytes
  let (productId, bytes) ← decodeUInt 1 bytes
  let (retransFlag, bytes) ← decodeUInt 1 bytes
  let (numBodyEntries, bytes) ← decodeUInt 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ msgSeqNum, sendTime, productId, retransFlag, numBodyEntries, filler, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
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
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | sequenceNumberResetMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SequenceNumberResetMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, HeartbeatMessage.encode_length]
    omega
  | messageUnavailableMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, MessageUnavailableMessage.encode_length]
    omega
  | refreshQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RefreshQuoteMessage.encode_length]
    omega
  | symbolIndexMappingMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SymbolIndexMappingMessage.encode_length]
    omega
  | quoteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, QuoteMessage.encode_length]
    omega

/-- Size rule: Msg Size counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

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

end Omi.NyseNysebondsQuotePdpV12A
