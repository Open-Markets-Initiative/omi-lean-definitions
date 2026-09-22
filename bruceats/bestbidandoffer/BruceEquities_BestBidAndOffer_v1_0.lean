import Omi.Wire

/-!
# Bruce ATS Best Bid And Offer v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BruceatsBruceequitiesBestbidandofferItchV10

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4D, 0x45, 0x43]

inductive EventCode where
  | startOfTransmissions -- Start Of Transmissions
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | endOfMarketHours -- End Of Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfTransmissions -- End Of Transmissions
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfTransmissions => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfMarketHours => 0x51
  | .endOfMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfTransmissions => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfTransmissions
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x45 then .endOfSystemHours
  else .endOfTransmissions

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfTransmissions => decide
  | startOfSystemHours => decide
  | startOfMarketHours => decide
  | endOfMarketHours => decide
  | endOfSystemHours => decide
  | endOfTransmissions => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Market Category: one byte code -/
def MarketCategory.codes : List UInt8 :=
  [0x41, 0x4E, 0x50, 0x51, 0x56, 0x5A, 0x20]

inductive MarketCategory where
  | nyseAmerican -- Nyse American
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | investorsExchangeLlc -- Investors Exchange Llc
  | cboeBzx -- Cboe Bzx
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCategory

def toByte : MarketCategory → UInt8
  | .nyseAmerican => 0x41
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .investorsExchangeLlc => 0x56
  | .cboeBzx => 0x5A
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCategory :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x56 then .investorsExchangeLlc
  else if byte = 0x5A then .cboeBzx
  else .notAvailable

def ofByte (byte : UInt8) : MarketCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCategory) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | investorsExchangeLlc => decide
  | cboeBzx => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCategory

/-- Authenticity: one byte code -/
def Authenticity.codes : List UInt8 :=
  [0x50, 0x54]

inductive Authenticity where
  | liveProduction -- Live Production
  | test -- Test
  | unlisted (byte : { byte : UInt8 // byte ∉ Authenticity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Authenticity

def toByte : Authenticity → UInt8
  | .liveProduction => 0x50
  | .test => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Authenticity :=
  if byte = 0x50 then .liveProduction
  else .test

def ofByte (byte : UInt8) : Authenticity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Authenticity) : ofByte value.toByte = value := by
  cases value with
  | liveProduction => decide
  | test => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Authenticity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Authenticity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Authenticity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Authenticity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Authenticity

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x48, 0x54]

inductive TradingState where
  | halted -- Halted
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .halted => 0x48
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x48 then .halted
  else .trading

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingState

/-- Reg Sho Action: one byte code -/
def RegShoAction.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive RegShoAction where
  | noPriceTestInPlace -- No Price Test In Place
  | regShoRestrictionInEffect -- Reg Sho Restriction In Effect
  | regShoRestrictionRemainsInEffect -- Reg Sho Restriction Remains In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ RegShoAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RegShoAction

def toByte : RegShoAction → UInt8
  | .noPriceTestInPlace => 0x30
  | .regShoRestrictionInEffect => 0x31
  | .regShoRestrictionRemainsInEffect => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RegShoAction :=
  if byte = 0x30 then .noPriceTestInPlace
  else if byte = 0x31 then .regShoRestrictionInEffect
  else .regShoRestrictionRemainsInEffect

def ofByte (byte : UInt8) : RegShoAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RegShoAction) : ofByte value.toByte = value := by
  cases value with
  | noPriceTestInPlace => decide
  | regShoRestrictionInEffect => decide
  | regShoRestrictionRemainsInEffect => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RegShoAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RegShoAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RegShoAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RegShoAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RegShoAction

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  stockLocate : BitVec 16
  timestamp : BitVec 64
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ (encodeUInt 8 message.timestamp
    ++ (EventCode.encode message.eventCode))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ stockLocate, timestamp, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Stock Directory: 24 bytes -/
structure StockDirectory where
  stockLocate : BitVec 16
  timestamp : BitVec 64
  stock : Alpha 8
  marketCategory : MarketCategory
  roundLotSize : BitVec 32
  authenticity : Authenticity
  deriving DecidableEq, Repr

namespace StockDirectory

def encode (message : StockDirectory) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ (encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (MarketCategory.encode message.marketCategory
    ++ (encodeUInt 4 message.roundLotSize
    ++ (Authenticity.encode message.authenticity)))))

def decode (bytes : List UInt8) : Option (StockDirectory × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (marketCategory, bytes) ← MarketCategory.decode bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (authenticity, bytes) ← Authenticity.decode bytes
  pure ({ stockLocate, timestamp, stock, marketCategory, roundLotSize, authenticity }, bytes)

@[simp] theorem encode_length (message : StockDirectory) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, MarketCategory.encode_length, Authenticity.encode_length]

theorem encode_length_pos (message : StockDirectory) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockDirectory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Authenticity.decode_encode, some_bind]
  rfl

end StockDirectory

/-- Stock Trading Action: 19 bytes -/
structure StockTradingAction where
  stockLocate : BitVec 16
  timestamp : BitVec 64
  stock : Alpha 8
  tradingState : TradingState
  deriving DecidableEq, Repr

namespace StockTradingAction

def encode (message : StockTradingAction) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ (encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (TradingState.encode message.tradingState)))

def decode (bytes : List UInt8) : Option (StockTradingAction × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  pure ({ stockLocate, timestamp, stock, tradingState }, bytes)

@[simp] theorem encode_length (message : StockTradingAction) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradingState.encode_length]

theorem encode_length_pos (message : StockTradingAction) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockTradingAction) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TradingState.decode_encode, some_bind]
  rfl

end StockTradingAction

/-- Reg Sho Short Sale Price Test Restricted Indicator: 19 bytes -/
structure RegShoShortSalePriceTestRestrictedIndicator where
  stockLocate : BitVec 16
  timestamp : BitVec 64
  stock : Alpha 8
  regShoAction : RegShoAction
  deriving DecidableEq, Repr

namespace RegShoShortSalePriceTestRestrictedIndicator

def encode (message : RegShoShortSalePriceTestRestrictedIndicator) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ (encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (RegShoAction.encode message.regShoAction)))

def decode (bytes : List UInt8) : Option (RegShoShortSalePriceTestRestrictedIndicator × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (regShoAction, bytes) ← RegShoAction.decode bytes
  pure ({ stockLocate, timestamp, stock, regShoAction }, bytes)

@[simp] theorem encode_length (message : RegShoShortSalePriceTestRestrictedIndicator) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, RegShoAction.encode_length]

theorem encode_length_pos (message : RegShoShortSalePriceTestRestrictedIndicator) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegShoShortSalePriceTestRestrictedIndicator) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RegShoAction.decode_encode, some_bind]
  rfl

end RegShoShortSalePriceTestRestrictedIndicator

/-- Quotation Message: 42 bytes -/
structure QuotationMessage where
  stockLocate : BitVec 16
  timestamp : BitVec 64
  stock : Alpha 8
  bestBidPrice : BitVec 64
  bestBidSize : BitVec 32
  bestOfferPrice : BitVec 64
  bestOfferSize : BitVec 32
  deriving DecidableEq, Repr

namespace QuotationMessage

def encode (message : QuotationMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ (encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 8 message.bestBidPrice
    ++ (encodeUInt 4 message.bestBidSize
    ++ (encodeUInt 8 message.bestOfferPrice
    ++ (encodeUInt 4 message.bestOfferSize))))))

def decode (bytes : List UInt8) : Option (QuotationMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (bestBidPrice, bytes) ← decodeUInt 8 bytes
  let (bestBidSize, bytes) ← decodeUInt 4 bytes
  let (bestOfferPrice, bytes) ← decodeUInt 8 bytes
  let (bestOfferSize, bytes) ← decodeUInt 4 bytes
  pure ({ stockLocate, timestamp, stock, bestBidPrice, bestBidSize, bestOfferPrice, bestOfferSize }, bytes)

@[simp] theorem encode_length (message : QuotationMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuotationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuotationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

end QuotationMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | stockDirectory (message : StockDirectory) -- "R" 0x52
  | stockTradingAction (message : StockTradingAction) -- "H" 0x48
  | regShoShortSalePriceTestRestrictedIndicator (message : RegShoShortSalePriceTestRestrictedIndicator) -- "Y" 0x59
  | quotationMessage (message : QuotationMessage) -- "Q" 0x51
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .stockDirectory _ => 82
  | .stockTradingAction _ => 72
  | .regShoShortSalePriceTestRestrictedIndicator _ => 89
  | .quotationMessage _ => 81

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .stockDirectory message => StockDirectory.encode message
  | .stockTradingAction message => StockTradingAction.encode message
  | .regShoShortSalePriceTestRestrictedIndicator message => RegShoShortSalePriceTestRestrictedIndicator.encode message
  | .quotationMessage message => QuotationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 42 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | stockDirectory inner =>
    simp only [encode, StockDirectory.encode_length]
    omega
  | stockTradingAction inner =>
    simp only [encode, StockTradingAction.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicator inner =>
    simp only [encode, RegShoShortSalePriceTestRestrictedIndicator.encode_length]
    omega
  | quotationMessage inner =>
    simp only [encode, QuotationMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (StockDirectory.decode bytes).map fun (message, rest) => (.stockDirectory message, rest)
  else if tag = 72 then (StockTradingAction.decode bytes).map fun (message, rest) => (.stockTradingAction message, rest)
  else if tag = 89 then (RegShoShortSalePriceTestRestrictedIndicator.decode bytes).map fun (message, rest) => (.regShoShortSalePriceTestRestrictedIndicator message, rest)
  else if tag = 81 then (QuotationMessage.decode bytes).map fun (message, rest) => (.quotationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | stockDirectory inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockDirectory.encode_length]
    omega
  | stockTradingAction inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockTradingAction.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicator inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RegShoShortSalePriceTestRestrictedIndicator.encode_length]
    omega
  | quotationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuotationMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
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
  session : Alpha 10
  sequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.BruceatsBruceequitiesBestbidandofferItchV10
