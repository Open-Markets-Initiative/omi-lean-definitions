import Wire

/-!
# Tradelogiq Markets Inc. Lynx Multicast Level 1 v1.01

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TradelogiqLynxatsMulticastlevel1ItchV101Udp

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4D, 0x45, 0x43, 0x42, 0x52]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | endOfMarketHours -- End Of Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | tradingHalted -- Trading Halted
  | tradingResumed -- Trading Resumed
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfMarketHours => 0x51
  | .endOfMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .tradingHalted => 0x42
  | .tradingResumed => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x45 then .endOfSystemHours
  else if byte = 0x43 then .endOfMessages
  else if byte = 0x42 then .tradingHalted
  else .tradingResumed

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfMarketHours => decide
  | endOfMarketHours => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
  | tradingHalted => decide
  | tradingResumed => decide
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

/-- Market: one byte code -/
def Market.codes : List UInt8 :=
  [0x74, 0x76, 0x63, 0x71, 0x6F, 0x7A]

inductive Market where
  | tsx -- Tsx
  | venture -- Venture
  | cnsx -- Cnsx
  | nasdaqCanada -- Nasdaq Canada
  | omega_ -- Omega
  | aequitas -- Aequitas
  | unlisted (byte : { byte : UInt8 // byte ∉ Market.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Market

def toByte : Market → UInt8
  | .tsx => 0x74
  | .venture => 0x76
  | .cnsx => 0x63
  | .nasdaqCanada => 0x71
  | .omega_ => 0x6F
  | .aequitas => 0x7A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Market :=
  if byte = 0x74 then .tsx
  else if byte = 0x76 then .venture
  else if byte = 0x63 then .cnsx
  else if byte = 0x71 then .nasdaqCanada
  else if byte = 0x6F then .omega_
  else .aequitas

def ofByte (byte : UInt8) : Market :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Market) : ofByte value.toByte = value := by
  cases value with
  | tsx => decide
  | venture => decide
  | cnsx => decide
  | nasdaqCanada => decide
  | omega_ => decide
  | aequitas => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Market) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Market × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Market) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Market) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Market

/-- Shortable: one byte code -/
def Shortable.codes : List UInt8 :=
  [0x45, 0x53, 0x4E]

inductive Shortable where
  | shortExempt -- Short Exempt
  | shortable -- Shortable
  | notShortable -- Not Shortable
  | unlisted (byte : { byte : UInt8 // byte ∉ Shortable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Shortable

def toByte : Shortable → UInt8
  | .shortExempt => 0x45
  | .shortable => 0x53
  | .notShortable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Shortable :=
  if byte = 0x45 then .shortExempt
  else if byte = 0x53 then .shortable
  else .notShortable

def ofByte (byte : UInt8) : Shortable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Shortable) : ofByte value.toByte = value := by
  cases value with
  | shortExempt => decide
  | shortable => decide
  | notShortable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Shortable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Shortable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Shortable) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Shortable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Shortable

/-- Dividend Indicator: one byte code -/
def DividendIndicator.codes : List UInt8 :=
  [0x41, 0x53, 0x51, 0x4D]

inductive DividendIndicator where
  | annual -- Annual
  | semiAnnual -- Semi Annual
  | quarterly -- Quarterly
  | monthly -- Monthly
  | unlisted (byte : { byte : UInt8 // byte ∉ DividendIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DividendIndicator

def toByte : DividendIndicator → UInt8
  | .annual => 0x41
  | .semiAnnual => 0x53
  | .quarterly => 0x51
  | .monthly => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DividendIndicator :=
  if byte = 0x41 then .annual
  else if byte = 0x53 then .semiAnnual
  else if byte = 0x51 then .quarterly
  else .monthly

def ofByte (byte : UInt8) : DividendIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DividendIndicator) : ofByte value.toByte = value := by
  cases value with
  | annual => decide
  | semiAnnual => decide
  | quarterly => decide
  | monthly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DividendIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DividendIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DividendIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DividendIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DividendIndicator

/-- Frequency: one byte code -/
def Frequency.codes : List UInt8 :=
  [0x41, 0x53, 0x51, 0x4D]

inductive Frequency where
  | annual -- Annual
  | semiAnnual -- Semi Annual
  | quarterly -- Quarterly
  | monthly -- Monthly
  | unlisted (byte : { byte : UInt8 // byte ∉ Frequency.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Frequency

def toByte : Frequency → UInt8
  | .annual => 0x41
  | .semiAnnual => 0x53
  | .quarterly => 0x51
  | .monthly => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Frequency :=
  if byte = 0x41 then .annual
  else if byte = 0x53 then .semiAnnual
  else if byte = 0x51 then .quarterly
  else .monthly

def ofByte (byte : UInt8) : Frequency :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Frequency) : ofByte value.toByte = value := by
  cases value with
  | annual => decide
  | semiAnnual => decide
  | quarterly => decide
  | monthly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Frequency) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Frequency × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Frequency) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Frequency) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Frequency

/-- Security Type: one byte code -/
def SecurityType.codes : List UInt8 :=
  [0x64, 0x72, 0x6E, 0x77]

inductive SecurityType where
  | debentures -- Debentures
  | rights -- Rights
  | notes -- Notes
  | warrants -- Warrants
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityType

def toByte : SecurityType → UInt8
  | .debentures => 0x64
  | .rights => 0x72
  | .notes => 0x6E
  | .warrants => 0x77
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityType :=
  if byte = 0x64 then .debentures
  else if byte = 0x72 then .rights
  else if byte = 0x6E then .notes
  else .warrants

def ofByte (byte : UInt8) : SecurityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityType) : ofByte value.toByte = value := by
  cases value with
  | debentures => decide
  | rights => decide
  | notes => decide
  | warrants => decide
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

/-- Quote Message: 43 bytes -/
structure QuoteMessage where
  reserved1 : Alpha 1
  stockSymbol : Alpha 10
  timestamp : BitVec 64
  bestBidPrice : BitVec 64
  bestBidSize : BitVec 32
  bestAskPrice : BitVec 64
  bestAskSize : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteMessage

def encode (message : QuoteMessage) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (Alpha.encode message.stockSymbol
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 8 message.bestBidPrice
    ++ (encodeUInt 4 message.bestBidSize
    ++ (encodeUInt 8 message.bestAskPrice
    ++ (encodeUInt 4 message.bestAskSize))))))

def decode (bytes : List UInt8) : Option (QuoteMessage × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (stockSymbol, bytes) ← Alpha.decode 10 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (bestBidPrice, bytes) ← decodeUInt 8 bytes
  let (bestBidSize, bytes) ← decodeUInt 4 bytes
  let (bestAskPrice, bytes) ← decodeUInt 8 bytes
  let (bestAskSize, bytes) ← decodeUInt 4 bytes
  pure ({ reserved1, stockSymbol, timestamp, bestBidPrice, bestBidSize, bestAskPrice, bestAskSize }, bytes)

@[simp] theorem encode_length (message : QuoteMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : QuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuoteMessage

/-- Trade Report Message: 43 bytes -/
structure TradeReportMessage where
  conditions : Alpha 5
  stockSymbol : Alpha 10
  timestamp : BitVec 64
  tradeId : BitVec 32
  tradePrice : BitVec 64
  tradeSize : BitVec 32
  buyBroker : BitVec 16
  sellBroker : BitVec 16
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  Alpha.encode message.conditions
    ++ (Alpha.encode message.stockSymbol
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.tradeId
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeSize
    ++ (encodeUInt 2 message.buyBroker
    ++ (encodeUInt 2 message.sellBroker)))))))

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (conditions, bytes) ← Alpha.decode 5 bytes
  let (stockSymbol, bytes) ← Alpha.decode 10 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (tradeId, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeSize, bytes) ← decodeUInt 4 bytes
  let (buyBroker, bytes) ← decodeUInt 2 bytes
  let (sellBroker, bytes) ← decodeUInt 2 bytes
  pure ({ conditions, stockSymbol, timestamp, tradeId, tradePrice, tradeSize, buyBroker, sellBroker }, bytes)

@[simp] theorem encode_length (message : TradeReportMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeReportMessage

/-- Trade Bust Message: 23 bytes -/
structure TradeBustMessage where
  reserved1 : Alpha 1
  stockSymbol : Alpha 10
  timestamp : BitVec 64
  tradeId : BitVec 32
  deriving DecidableEq, Repr

namespace TradeBustMessage

def encode (message : TradeBustMessage) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (Alpha.encode message.stockSymbol
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.tradeId)))

def decode (bytes : List UInt8) : Option (TradeBustMessage × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (stockSymbol, bytes) ← Alpha.decode 10 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (tradeId, bytes) ← decodeUInt 4 bytes
  pure ({ reserved1, stockSymbol, timestamp, tradeId }, bytes)

@[simp] theorem encode_length (message : TradeBustMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeBustMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeBustMessage

/-- Trade Correction Message: 47 bytes -/
structure TradeCorrectionMessage where
  reserved1 : Alpha 1
  stockSymbol : Alpha 10
  timestamp : BitVec 64
  originalTradeId : BitVec 32
  originalTradePrice : BitVec 64
  originalTradeSize : BitVec 32
  correctedTradePrice : BitVec 64
  correctedTradeSize : BitVec 32
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (Alpha.encode message.stockSymbol
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.originalTradeId
    ++ (encodeUInt 8 message.originalTradePrice
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (encodeUInt 8 message.correctedTradePrice
    ++ (encodeUInt 4 message.correctedTradeSize)))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (stockSymbol, bytes) ← Alpha.decode 10 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (originalTradeId, bytes) ← decodeUInt 4 bytes
  let (originalTradePrice, bytes) ← decodeUInt 8 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (correctedTradePrice, bytes) ← decodeUInt 8 bytes
  let (correctedTradeSize, bytes) ← decodeUInt 4 bytes
  pure ({ reserved1, stockSymbol, timestamp, originalTradeId, originalTradePrice, originalTradeSize, correctedTradePrice, correctedTradeSize }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCorrectionMessage

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  eventCode : EventCode
  reserved2 : Alpha 2
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  EventCode.encode message.eventCode
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.timestamp))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (eventCode, bytes) ← EventCode.decode bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  pure ({ eventCode, reserved2, timestamp }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, EventCode.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Stock Directory Message: 39 bytes -/
structure StockDirectoryMessage where
  market : Market
  stock : Alpha 10
  timestamp : BitVec 64
  boardLotSize : BitVec 32
  instrumentId : BitVec 16
  shortable : Shortable
  dividendIndicator : DividendIndicator
  reserved9 : Alpha 9
  currency : Alpha 3
  deriving DecidableEq, Repr

namespace StockDirectoryMessage

def encode (message : StockDirectoryMessage) : List UInt8 :=
  Market.encode message.market
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.boardLotSize
    ++ (encodeUInt 2 message.instrumentId
    ++ (Shortable.encode message.shortable
    ++ (DividendIndicator.encode message.dividendIndicator
    ++ (Alpha.encode message.reserved9
    ++ (Alpha.encode message.currency))))))))

def decode (bytes : List UInt8) : Option (StockDirectoryMessage × List UInt8) := do
  let (market, bytes) ← Market.decode bytes
  let (stock, bytes) ← Alpha.decode 10 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (boardLotSize, bytes) ← decodeUInt 4 bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (shortable_, bytes) ← Shortable.decode bytes
  let (dividendIndicator, bytes) ← DividendIndicator.decode bytes
  let (reserved9, bytes) ← Alpha.decode 9 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  pure ({ market, stock, timestamp, boardLotSize, instrumentId, shortable := shortable_, dividendIndicator, reserved9, currency }, bytes)

@[simp] theorem encode_length (message : StockDirectoryMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, Market.encode_length, Alpha.encode_length, encodeUInt_length, Shortable.encode_length, DividendIndicator.encode_length]

theorem encode_length_pos (message : StockDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Shortable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DividendIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockDirectoryMessage

/-- Extended Stock Directory Message: 71 bytes -/
structure ExtendedStockDirectoryMessage where
  market : Market
  stock : Alpha 10
  timestamp : BitVec 64
  boardLotSize : BitVec 32
  instrumentId : BitVec 16
  shortable : Shortable
  frequency : Frequency
  reserved9 : Alpha 9
  currency : Alpha 3
  securityType : SecurityType
  expiryDate : Alpha 8
  description : Alpha 20
  reserved3 : Alpha 3
  deriving DecidableEq, Repr

namespace ExtendedStockDirectoryMessage

def encode (message : ExtendedStockDirectoryMessage) : List UInt8 :=
  Market.encode message.market
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.boardLotSize
    ++ (encodeUInt 2 message.instrumentId
    ++ (Shortable.encode message.shortable
    ++ (Frequency.encode message.frequency
    ++ (Alpha.encode message.reserved9
    ++ (Alpha.encode message.currency
    ++ (SecurityType.encode message.securityType
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.description
    ++ (Alpha.encode message.reserved3))))))))))))

def decode (bytes : List UInt8) : Option (ExtendedStockDirectoryMessage × List UInt8) := do
  let (market, bytes) ← Market.decode bytes
  let (stock, bytes) ← Alpha.decode 10 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (boardLotSize, bytes) ← decodeUInt 4 bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (shortable_, bytes) ← Shortable.decode bytes
  let (frequency, bytes) ← Frequency.decode bytes
  let (reserved9, bytes) ← Alpha.decode 9 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (securityType, bytes) ← SecurityType.decode bytes
  let (expiryDate, bytes) ← Alpha.decode 8 bytes
  let (description, bytes) ← Alpha.decode 20 bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ market, stock, timestamp, boardLotSize, instrumentId, shortable := shortable_, frequency, reserved9, currency, securityType, expiryDate, description, reserved3 }, bytes)

@[simp] theorem encode_length (message : ExtendedStockDirectoryMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, Market.encode_length, Alpha.encode_length, encodeUInt_length, Shortable.encode_length, Frequency.encode_length, SecurityType.encode_length]

theorem encode_length_pos (message : ExtendedStockDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExtendedStockDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Shortable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Frequency.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExtendedStockDirectoryMessage

/-- Stock Status Message: 23 bytes -/
structure StockStatusMessage where
  tradingState : TradingState
  stock : Alpha 10
  timestamp : BitVec 64
  reason : Alpha 4
  deriving DecidableEq, Repr

namespace StockStatusMessage

def encode (message : StockStatusMessage) : List UInt8 :=
  TradingState.encode message.tradingState
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.reason)))

def decode (bytes : List UInt8) : Option (StockStatusMessage × List UInt8) := do
  let (tradingState, bytes) ← TradingState.decode bytes
  let (stock, bytes) ← Alpha.decode 10 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (reason, bytes) ← Alpha.decode 4 bytes
  pure ({ tradingState, stock, timestamp, reason }, bytes)

@[simp] theorem encode_length (message : StockStatusMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, TradingState.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StockStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TradingState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockStatusMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | quoteMessage (message : QuoteMessage) -- "W" 0x57
  | tradeReportMessage (message : TradeReportMessage) -- "T" 0x54
  | tradeBustMessage (message : TradeBustMessage) -- "N" 0x4E
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "M" 0x4D
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | stockDirectoryMessage (message : StockDirectoryMessage) -- "R" 0x52
  | extendedStockDirectoryMessage (message : ExtendedStockDirectoryMessage) -- "r" 0x72
  | stockStatusMessage (message : StockStatusMessage) -- "H" 0x48
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .quoteMessage _ => 87
  | .tradeReportMessage _ => 84
  | .tradeBustMessage _ => 78
  | .tradeCorrectionMessage _ => 77
  | .systemEventMessage _ => 83
  | .stockDirectoryMessage _ => 82
  | .extendedStockDirectoryMessage _ => 114
  | .stockStatusMessage _ => 72

def encode : Payload → List UInt8
  | .quoteMessage message => QuoteMessage.encode message
  | .tradeReportMessage message => TradeReportMessage.encode message
  | .tradeBustMessage message => TradeBustMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .extendedStockDirectoryMessage message => ExtendedStockDirectoryMessage.encode message
  | .stockStatusMessage message => StockStatusMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 71 := by
  cases message with
  | quoteMessage inner =>
    simp only [encode, QuoteMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [encode, TradeReportMessage.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [encode, TradeBustMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [encode, StockDirectoryMessage.encode_length]
    omega
  | extendedStockDirectoryMessage inner =>
    simp only [encode, ExtendedStockDirectoryMessage.encode_length]
    omega
  | stockStatusMessage inner =>
    simp only [encode, StockStatusMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 87 then (QuoteMessage.decode bytes).map fun (message, rest) => (.quoteMessage message, rest)
  else if tag = 84 then (TradeReportMessage.decode bytes).map fun (message, rest) => (.tradeReportMessage message, rest)
  else if tag = 78 then (TradeBustMessage.decode bytes).map fun (message, rest) => (.tradeBustMessage message, rest)
  else if tag = 77 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 114 then (ExtendedStockDirectoryMessage.decode bytes).map fun (message, rest) => (.extendedStockDirectoryMessage message, rest)
  else if tag = 72 then (StockStatusMessage.decode bytes).map fun (message, rest) => (.stockStatusMessage message, rest)
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
  | quoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeReportMessage.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeBustMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeCorrectionMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockDirectoryMessage.encode_length]
    omega
  | extendedStockDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExtendedStockDirectoryMessage.encode_length]
    omega
  | stockStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockStatusMessage.encode_length]
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

end Omi.TradelogiqLynxatsMulticastlevel1ItchV101Udp
