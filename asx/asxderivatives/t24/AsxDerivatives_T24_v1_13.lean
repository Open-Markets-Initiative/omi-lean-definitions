import Omi.Wire

/-!
# Australian Securities Exchange 24 Itch v1.13

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: Market Updates is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.AsxAsxderivativesT24ItchV113

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x43, 0x50, 0x52]

inductive EventCode where
  | open_ -- Open
  | start -- Start
  | end_ -- End
  | paused -- Paused
  | resumed -- Resumed
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .open_ => 0x4F
  | .start => 0x53
  | .end_ => 0x43
  | .paused => 0x50
  | .resumed => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .open_
  else if byte = 0x53 then .start
  else if byte = 0x43 then .end_
  else if byte = 0x50 then .paused
  else .resumed

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | start => decide
  | end_ => decide
  | paused => decide
  | resumed => decide
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

/-- Contract Type: one byte code -/
def ContractType.codes : List UInt8 :=
  [0x46, 0x4F, 0x45, 0x4E, 0x53, 0x41, 0x44]

inductive ContractType where
  | cfut -- Cfut
  | copta -- Copta
  | eopta -- Eopta
  | oopt -- Oopt
  | csprd -- Csprd
  | sprd -- Sprd
  | sfut -- Sfut
  | unlisted (byte : { byte : UInt8 // byte ∉ ContractType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContractType

def toByte : ContractType → UInt8
  | .cfut => 0x46
  | .copta => 0x4F
  | .eopta => 0x45
  | .oopt => 0x4E
  | .csprd => 0x53
  | .sprd => 0x41
  | .sfut => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContractType :=
  if byte = 0x46 then .cfut
  else if byte = 0x4F then .copta
  else if byte = 0x45 then .eopta
  else if byte = 0x4E then .oopt
  else if byte = 0x53 then .csprd
  else if byte = 0x41 then .sprd
  else .sfut

def ofByte (byte : UInt8) : ContractType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContractType) : ofByte value.toByte = value := by
  cases value with
  | cfut => decide
  | copta => decide
  | eopta => decide
  | oopt => decide
  | csprd => decide
  | sprd => decide
  | sfut => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContractType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContractType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContractType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ContractType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContractType

/-- Financial Type: one byte code -/
def FinancialType.codes : List UInt8 :=
  [0x43, 0x44, 0x45, 0x58, 0x42]

inductive FinancialType where
  | commodity -- Commodity
  | cfd -- Cfd
  | equity -- Equity
  | governmentBond -- Government Bond
  | bankBill -- Bank Bill
  | unlisted (byte : { byte : UInt8 // byte ∉ FinancialType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinancialType

def toByte : FinancialType → UInt8
  | .commodity => 0x43
  | .cfd => 0x44
  | .equity => 0x45
  | .governmentBond => 0x58
  | .bankBill => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinancialType :=
  if byte = 0x43 then .commodity
  else if byte = 0x44 then .cfd
  else if byte = 0x45 then .equity
  else if byte = 0x58 then .governmentBond
  else .bankBill

def ofByte (byte : UInt8) : FinancialType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinancialType) : ofByte value.toByte = value := by
  cases value with
  | commodity => decide
  | cfd => decide
  | equity => decide
  | governmentBond => decide
  | bankBill => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FinancialType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinancialType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinancialType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FinancialType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinancialType

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x50, 0x43]

inductive OptionType where
  | put -- Put
  | call -- Call
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .put => 0x50
  | .call => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x50 then .put
  else .call

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | put => decide
  | call => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

/-- Activated: one byte code -/
def Activated.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Activated where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ Activated.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Activated

def toByte : Activated → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Activated :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : Activated :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Activated) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Activated) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Activated × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Activated) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Activated) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Activated

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x70, 0x48, 0x50, 0x43, 0x6C, 0x4C, 0x4F, 0x55, 0x64, 0x49, 0x44, 0x41, 0x52]

inductive TradingStatus where
  | pending -- Pending
  | halted -- Halted
  | preOpen -- Pre Open
  | closed -- Closed
  | levelling -- Levelling
  | locked -- Locked
  | opened -- Opened
  | unavailable -- Unavailable
  | prePriceDiscovery -- Pre Price Discovery
  | inactive -- Inactive
  | priceDiscovery -- Price Discovery
  | activated -- Activated
  | regulatoryHalt -- Regulatory Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .pending => 0x70
  | .halted => 0x48
  | .preOpen => 0x50
  | .closed => 0x43
  | .levelling => 0x6C
  | .locked => 0x4C
  | .opened => 0x4F
  | .unavailable => 0x55
  | .prePriceDiscovery => 0x64
  | .inactive => 0x49
  | .priceDiscovery => 0x44
  | .activated => 0x41
  | .regulatoryHalt => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x70 then .pending
  else if byte = 0x48 then .halted
  else if byte = 0x50 then .preOpen
  else if byte = 0x43 then .closed
  else if byte = 0x6C then .levelling
  else if byte = 0x4C then .locked
  else if byte = 0x4F then .opened
  else if byte = 0x55 then .unavailable
  else if byte = 0x64 then .prePriceDiscovery
  else if byte = 0x49 then .inactive
  else if byte = 0x44 then .priceDiscovery
  else if byte = 0x41 then .activated
  else .regulatoryHalt

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | pending => decide
  | halted => decide
  | preOpen => decide
  | closed => decide
  | levelling => decide
  | locked => decide
  | opened => decide
  | unavailable => decide
  | prePriceDiscovery => decide
  | inactive => decide
  | priceDiscovery => decide
  | activated => decide
  | regulatoryHalt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingStatus

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x53, 0x42]

inductive Side where
  | sell -- Sell
  | buy -- Buy
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .sell => 0x53
  | .buy => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x53 then .sell
  else .buy

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | sell => decide
  | buy => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x54, 0x74, 0x57, 0x77, 0x4C, 0x6C, 0x53, 0x73, 0x52, 0x72, 0x51, 0x71, 0x55, 0x75]

inductive TradeType where
  | normal -- Normal
  | crossingNormal -- Crossing Normal
  | sweeping -- Sweeping
  | crossingSweeping -- Crossing Sweeping
  | levelling -- Levelling
  | crossingLevelling -- Crossing Levelling
  | spreadToUnderlying -- Spread To Underlying
  | crossingSpreadToUnderlying -- Crossing Spread To Underlying
  | intraSpread -- Intra Spread
  | crossingIntraSpread -- Crossing Intra Spread
  | interSpread -- Inter Spread
  | crossingInterSpread -- Crossing Inter Spread
  | custom -- Custom
  | crossingCustom -- Crossing Custom
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .normal => 0x54
  | .crossingNormal => 0x74
  | .sweeping => 0x57
  | .crossingSweeping => 0x77
  | .levelling => 0x4C
  | .crossingLevelling => 0x6C
  | .spreadToUnderlying => 0x53
  | .crossingSpreadToUnderlying => 0x73
  | .intraSpread => 0x52
  | .crossingIntraSpread => 0x72
  | .interSpread => 0x51
  | .crossingInterSpread => 0x71
  | .custom => 0x55
  | .crossingCustom => 0x75
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x54 then .normal
  else if byte = 0x74 then .crossingNormal
  else if byte = 0x57 then .sweeping
  else if byte = 0x77 then .crossingSweeping
  else if byte = 0x4C then .levelling
  else if byte = 0x6C then .crossingLevelling
  else if byte = 0x53 then .spreadToUnderlying
  else if byte = 0x73 then .crossingSpreadToUnderlying
  else if byte = 0x52 then .intraSpread
  else if byte = 0x72 then .crossingIntraSpread
  else if byte = 0x51 then .interSpread
  else if byte = 0x71 then .crossingInterSpread
  else if byte = 0x55 then .custom
  else .crossingCustom

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | normal => decide
  | crossingNormal => decide
  | sweeping => decide
  | crossingSweeping => decide
  | levelling => decide
  | crossingLevelling => decide
  | spreadToUnderlying => decide
  | crossingSpreadToUnderlying => decide
  | intraSpread => decide
  | crossingIntraSpread => decide
  | interSpread => decide
  | crossingInterSpread => decide
  | custom => decide
  | crossingCustom => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeType

/-- Printable: one byte code -/
def Printable.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Printable where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ Printable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Printable

def toByte : Printable → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Printable :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : Printable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Printable) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Printable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Printable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Printable) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Printable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Printable

/-- Session: 10 bytes -/
structure Session where
  protocolVersion : Alpha 3
  sessionYear : Alpha 2
  sessionWeek : Alpha 2
  tradingService : Alpha 3
  deriving DecidableEq, Repr

namespace Session

def encode (message : Session) : List UInt8 :=
  Alpha.encode message.protocolVersion
    ++ (Alpha.encode message.sessionYear
    ++ (Alpha.encode message.sessionWeek
    ++ (Alpha.encode message.tradingService)))

def decode (bytes : List UInt8) : Option (Session × List UInt8) := do
  let (protocolVersion, bytes) ← Alpha.decode 3 bytes
  let (sessionYear, bytes) ← Alpha.decode 2 bytes
  let (sessionWeek, bytes) ← Alpha.decode 2 bytes
  let (tradingService, bytes) ← Alpha.decode 3 bytes
  pure ({ protocolVersion, sessionYear, sessionWeek, tradingService }, bytes)

@[simp] theorem encode_length (message : Session) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : Session) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Session) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Session

/-- Time Message: 4 bytes -/
structure TimeMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace TimeMessage

def encode (message : TimeMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (TimeMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : TimeMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : TimeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TimeMessage

/-- System Event Message: 7 bytes -/
structure SystemEventMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (EventCode.encode message.eventCode))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ nanoseconds, tradeDate, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 7 := by
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

/-- Future Symbol Directory Message: 53 bytes -/
structure FutureSymbolDirectoryMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  exchange : Alpha 6
  instrument : Alpha 6
  contractType : ContractType
  expiryYear : BitVec 16
  expiryMonth : BitVec 8
  priceDecimalPosition : BitVec 8
  priceFractionalDenominator : BitVec 32
  priceMinimumTick : BitVec 16
  lastTradingDate : BitVec 32
  priorDaySettlement : BitVec 32
  financialType : FinancialType
  currency : Alpha 3
  lotSizeOrFaceValue : BitVec 32
  maturityValue : BitVec 8
  couponRate : BitVec 16
  paymentsPerYear : BitVec 8
  deriving DecidableEq, Repr

namespace FutureSymbolDirectoryMessage

def encode (message : FutureSymbolDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Alpha.encode message.exchange
    ++ (Alpha.encode message.instrument
    ++ (ContractType.encode message.contractType
    ++ (encodeUInt 2 message.expiryYear
    ++ (encodeUInt 1 message.expiryMonth
    ++ (encodeUInt 1 message.priceDecimalPosition
    ++ (encodeUInt 4 message.priceFractionalDenominator
    ++ (encodeUInt 2 message.priceMinimumTick
    ++ (encodeUInt 4 message.lastTradingDate
    ++ (encodeUInt 4 message.priorDaySettlement
    ++ (FinancialType.encode message.financialType
    ++ (Alpha.encode message.currency
    ++ (encodeUInt 4 message.lotSizeOrFaceValue
    ++ (encodeUInt 1 message.maturityValue
    ++ (encodeUInt 2 message.couponRate
    ++ (encodeUInt 1 message.paymentsPerYear))))))))))))))))))

def decode (bytes : List UInt8) : Option (FutureSymbolDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (exchange, bytes) ← Alpha.decode 6 bytes
  let (instrument, bytes) ← Alpha.decode 6 bytes
  let (contractType, bytes) ← ContractType.decode bytes
  let (expiryYear, bytes) ← decodeUInt 2 bytes
  let (expiryMonth, bytes) ← decodeUInt 1 bytes
  let (priceDecimalPosition, bytes) ← decodeUInt 1 bytes
  let (priceFractionalDenominator, bytes) ← decodeUInt 4 bytes
  let (priceMinimumTick, bytes) ← decodeUInt 2 bytes
  let (lastTradingDate, bytes) ← decodeUInt 4 bytes
  let (priorDaySettlement, bytes) ← decodeUInt 4 bytes
  let (financialType, bytes) ← FinancialType.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (lotSizeOrFaceValue, bytes) ← decodeUInt 4 bytes
  let (maturityValue, bytes) ← decodeUInt 1 bytes
  let (couponRate, bytes) ← decodeUInt 2 bytes
  let (paymentsPerYear, bytes) ← decodeUInt 1 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, exchange, instrument, contractType, expiryYear, expiryMonth, priceDecimalPosition, priceFractionalDenominator, priceMinimumTick, lastTradingDate, priorDaySettlement, financialType, currency, lotSizeOrFaceValue, maturityValue, couponRate, paymentsPerYear }, bytes)

@[simp] theorem encode_length (message : FutureSymbolDirectoryMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ContractType.encode_length, FinancialType.encode_length]

theorem encode_length_pos (message : FutureSymbolDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureSymbolDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ContractType.decode_encode, some_bind]
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
  rw [List.append_assoc, FinancialType.decode_encode, some_bind]
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

end FutureSymbolDirectoryMessage

/-- Spread Symbol Directory Message: 34 bytes -/
structure SpreadSymbolDirectoryMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  exchange : Alpha 6
  contractType : ContractType
  firstLegContractNumber : BitVec 32
  secondLegContractNumber : BitVec 32
  primaryRatio : BitVec 8
  secondaryRatio : BitVec 8
  priceDecimalPosition : BitVec 8
  priceFractionalDenominator : BitVec 32
  priceMinimumTick : BitVec 16
  deriving DecidableEq, Repr

namespace SpreadSymbolDirectoryMessage

def encode (message : SpreadSymbolDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Alpha.encode message.exchange
    ++ (ContractType.encode message.contractType
    ++ (encodeUInt 4 message.firstLegContractNumber
    ++ (encodeUInt 4 message.secondLegContractNumber
    ++ (encodeUInt 1 message.primaryRatio
    ++ (encodeUInt 1 message.secondaryRatio
    ++ (encodeUInt 1 message.priceDecimalPosition
    ++ (encodeUInt 4 message.priceFractionalDenominator
    ++ (encodeUInt 2 message.priceMinimumTick)))))))))))

def decode (bytes : List UInt8) : Option (SpreadSymbolDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (exchange, bytes) ← Alpha.decode 6 bytes
  let (contractType, bytes) ← ContractType.decode bytes
  let (firstLegContractNumber, bytes) ← decodeUInt 4 bytes
  let (secondLegContractNumber, bytes) ← decodeUInt 4 bytes
  let (primaryRatio, bytes) ← decodeUInt 1 bytes
  let (secondaryRatio, bytes) ← decodeUInt 1 bytes
  let (priceDecimalPosition, bytes) ← decodeUInt 1 bytes
  let (priceFractionalDenominator, bytes) ← decodeUInt 4 bytes
  let (priceMinimumTick, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, exchange, contractType, firstLegContractNumber, secondLegContractNumber, primaryRatio, secondaryRatio, priceDecimalPosition, priceFractionalDenominator, priceMinimumTick }, bytes)

@[simp] theorem encode_length (message : SpreadSymbolDirectoryMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ContractType.encode_length]

theorem encode_length_pos (message : SpreadSymbolDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadSymbolDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ContractType.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SpreadSymbolDirectoryMessage

/-- Option Symbol Directory Message: 74 bytes -/
structure OptionSymbolDirectoryMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  exchange : Alpha 6
  instrument : Alpha 6
  contractType : ContractType
  expiryYear : BitVec 16
  expiryMonth : BitVec 8
  optionType : OptionType
  strike : BitVec 32
  underlyingContractNumber : BitVec 32
  priceDecimalPosition : BitVec 8
  priceFractionalDenominator : BitVec 32
  priceMinimumTick : BitVec 16
  strikePriceDecimalPosition : BitVec 8
  strikePriceFractionalDenominator : BitVec 32
  strikePriceMinimumTick : BitVec 16
  lastTradingDate : BitVec 32
  priorDaySettlement : BitVec 32
  volatility : BitVec 32
  financialType : FinancialType
  currency : Alpha 3
  lotSizeOrFaceValue : BitVec 32
  maturityValue : BitVec 8
  couponRate : BitVec 16
  paymentsPerYear : BitVec 8
  activated : Activated
  deriving DecidableEq, Repr

namespace OptionSymbolDirectoryMessage

def encode (message : OptionSymbolDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Alpha.encode message.exchange
    ++ (Alpha.encode message.instrument
    ++ (ContractType.encode message.contractType
    ++ (encodeUInt 2 message.expiryYear
    ++ (encodeUInt 1 message.expiryMonth
    ++ (OptionType.encode message.optionType
    ++ (encodeUInt 4 message.strike
    ++ (encodeUInt 4 message.underlyingContractNumber
    ++ (encodeUInt 1 message.priceDecimalPosition
    ++ (encodeUInt 4 message.priceFractionalDenominator
    ++ (encodeUInt 2 message.priceMinimumTick
    ++ (encodeUInt 1 message.strikePriceDecimalPosition
    ++ (encodeUInt 4 message.strikePriceFractionalDenominator
    ++ (encodeUInt 2 message.strikePriceMinimumTick
    ++ (encodeUInt 4 message.lastTradingDate
    ++ (encodeUInt 4 message.priorDaySettlement
    ++ (encodeUInt 4 message.volatility
    ++ (FinancialType.encode message.financialType
    ++ (Alpha.encode message.currency
    ++ (encodeUInt 4 message.lotSizeOrFaceValue
    ++ (encodeUInt 1 message.maturityValue
    ++ (encodeUInt 2 message.couponRate
    ++ (encodeUInt 1 message.paymentsPerYear
    ++ (Activated.encode message.activated))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OptionSymbolDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (exchange, bytes) ← Alpha.decode 6 bytes
  let (instrument, bytes) ← Alpha.decode 6 bytes
  let (contractType, bytes) ← ContractType.decode bytes
  let (expiryYear, bytes) ← decodeUInt 2 bytes
  let (expiryMonth, bytes) ← decodeUInt 1 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (strike, bytes) ← decodeUInt 4 bytes
  let (underlyingContractNumber, bytes) ← decodeUInt 4 bytes
  let (priceDecimalPosition, bytes) ← decodeUInt 1 bytes
  let (priceFractionalDenominator, bytes) ← decodeUInt 4 bytes
  let (priceMinimumTick, bytes) ← decodeUInt 2 bytes
  let (strikePriceDecimalPosition, bytes) ← decodeUInt 1 bytes
  let (strikePriceFractionalDenominator, bytes) ← decodeUInt 4 bytes
  let (strikePriceMinimumTick, bytes) ← decodeUInt 2 bytes
  let (lastTradingDate, bytes) ← decodeUInt 4 bytes
  let (priorDaySettlement, bytes) ← decodeUInt 4 bytes
  let (volatility, bytes) ← decodeUInt 4 bytes
  let (financialType, bytes) ← FinancialType.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (lotSizeOrFaceValue, bytes) ← decodeUInt 4 bytes
  let (maturityValue, bytes) ← decodeUInt 1 bytes
  let (couponRate, bytes) ← decodeUInt 2 bytes
  let (paymentsPerYear, bytes) ← decodeUInt 1 bytes
  let (activated, bytes) ← Activated.decode bytes
  pure ({ nanoseconds, tradeDate, contractNumber, exchange, instrument, contractType, expiryYear, expiryMonth, optionType, strike, underlyingContractNumber, priceDecimalPosition, priceFractionalDenominator, priceMinimumTick, strikePriceDecimalPosition, strikePriceFractionalDenominator, strikePriceMinimumTick, lastTradingDate, priorDaySettlement, volatility, financialType, currency, lotSizeOrFaceValue, maturityValue, couponRate, paymentsPerYear, activated }, bytes)

@[simp] theorem encode_length (message : OptionSymbolDirectoryMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ContractType.encode_length, OptionType.encode_length, FinancialType.encode_length, Activated.encode_length]

theorem encode_length_pos (message : OptionSymbolDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OptionSymbolDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ContractType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialType.decode_encode, some_bind]
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
  rw [Activated.decode_encode, some_bind]
  rfl

end OptionSymbolDirectoryMessage

/-- Order Book State Message: 11 bytes -/
structure OrderBookStateMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  tradingStatus : TradingStatus
  deriving DecidableEq, Repr

namespace OrderBookStateMessage

def encode (message : OrderBookStateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (TradingStatus.encode message.tradingStatus)))

def decode (bytes : List UInt8) : Option (OrderBookStateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  pure ({ nanoseconds, tradeDate, contractNumber, tradingStatus }, bytes)

@[simp] theorem encode_length (message : OrderBookStateMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingStatus.encode_length]

theorem encode_length_pos (message : OrderBookStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TradingStatus.decode_encode, some_bind]
  rfl

end OrderBookStateMessage

/-- Order Added Message: 31 bytes -/
structure OrderAddedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  side : Side
  orderNumber : BitVec 64
  orderBookPriority : BitVec 32
  quantity : BitVec 32
  price : BitVec 32
  deriving DecidableEq, Repr

namespace OrderAddedMessage

def encode (message : OrderAddedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.orderBookPriority
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.price)))))))

def decode (bytes : List UInt8) : Option (OrderAddedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (orderBookPriority, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, side, orderNumber, orderBookPriority, quantity, price }, bytes)

@[simp] theorem encode_length (message : OrderAddedMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderAddedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderAddedMessage

/-- Order Replaced Message: 31 bytes -/
structure OrderReplacedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  side : Side
  orderNumber : BitVec 64
  orderBookPriority : BitVec 32
  quantity : BitVec 32
  price : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReplacedMessage

def encode (message : OrderReplacedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.orderBookPriority
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.price)))))))

def decode (bytes : List UInt8) : Option (OrderReplacedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (orderBookPriority, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, side, orderNumber, orderBookPriority, quantity, price }, bytes)

@[simp] theorem encode_length (message : OrderReplacedMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderReplacedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderReplacedMessage

/-- Order Volume Cancelled Message: 23 bytes -/
structure OrderVolumeCancelledMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  side : Side
  orderNumber : BitVec 64
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace OrderVolumeCancelledMessage

def encode (message : OrderVolumeCancelledMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (OrderVolumeCancelledMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, side, orderNumber, quantity }, bytes)

@[simp] theorem encode_length (message : OrderVolumeCancelledMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderVolumeCancelledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderVolumeCancelledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderVolumeCancelledMessage

/-- Order Deleted Message: 19 bytes -/
structure OrderDeletedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  side : Side
  orderNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeletedMessage

def encode (message : OrderDeletedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderNumber))))

def decode (bytes : List UInt8) : Option (OrderDeletedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, side, orderNumber }, bytes)

@[simp] theorem encode_length (message : OrderDeletedMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderDeletedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeletedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeletedMessage

/-- Implied Order Added Message: 31 bytes -/
structure ImpliedOrderAddedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  side : Side
  orderNumber : BitVec 64
  orderBookPriority : BitVec 32
  quantity : BitVec 32
  price : BitVec 32
  deriving DecidableEq, Repr

namespace ImpliedOrderAddedMessage

def encode (message : ImpliedOrderAddedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.orderBookPriority
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.price)))))))

def decode (bytes : List UInt8) : Option (ImpliedOrderAddedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (orderBookPriority, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, side, orderNumber, orderBookPriority, quantity, price }, bytes)

@[simp] theorem encode_length (message : ImpliedOrderAddedMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : ImpliedOrderAddedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImpliedOrderAddedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ImpliedOrderAddedMessage

/-- Implied Order Replaced Message: 31 bytes -/
structure ImpliedOrderReplacedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  side : Side
  orderNumber : BitVec 64
  orderBookPriority : BitVec 32
  quantity : BitVec 32
  price : BitVec 32
  deriving DecidableEq, Repr

namespace ImpliedOrderReplacedMessage

def encode (message : ImpliedOrderReplacedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.orderBookPriority
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.price)))))))

def decode (bytes : List UInt8) : Option (ImpliedOrderReplacedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (orderBookPriority, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, side, orderNumber, orderBookPriority, quantity, price }, bytes)

@[simp] theorem encode_length (message : ImpliedOrderReplacedMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : ImpliedOrderReplacedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImpliedOrderReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ImpliedOrderReplacedMessage

/-- Implied Order Deleted Message: 19 bytes -/
structure ImpliedOrderDeletedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  side : Side
  orderNumber : BitVec 64
  deriving DecidableEq, Repr

namespace ImpliedOrderDeletedMessage

def encode (message : ImpliedOrderDeletedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderNumber))))

def decode (bytes : List UInt8) : Option (ImpliedOrderDeletedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, side, orderNumber }, bytes)

@[simp] theorem encode_length (message : ImpliedOrderDeletedMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : ImpliedOrderDeletedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImpliedOrderDeletedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ImpliedOrderDeletedMessage

/-- Contract Legs: 11 bytes -/
structure ContractLegs where
  contractNumber : BitVec 32
  side : Side
  ratio : BitVec 16
  price : BitVec 32
  deriving DecidableEq, Repr

namespace ContractLegs

def encode (message : ContractLegs) : List UInt8 :=
  encodeUInt 4 message.contractNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 2 message.ratio
    ++ (encodeUInt 4 message.price)))

def decode (bytes : List UInt8) : Option (ContractLegs × List UInt8) := do
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (ratio, bytes) ← decodeUInt 2 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ contractNumber, side, ratio, price }, bytes)

@[simp] theorem encode_length (message : ContractLegs) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : ContractLegs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractLegs) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ContractLegs

/-- Custom Market Order Added Message: 89 bytes -/
structure CustomMarketOrderAddedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  orderNumber : BitVec 64
  orderBookPriority : BitVec 32
  quantity : BitVec 32
  legs : BitVec 8
  contractLegs : Exact 6 ContractLegs
  deriving DecidableEq, Repr

namespace CustomMarketOrderAddedMessage

def encode (message : CustomMarketOrderAddedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.orderBookPriority
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 1 message.legs
    ++ (encodeMany ContractLegs.encode message.contractLegs.val))))))

def decode (bytes : List UInt8) : Option (CustomMarketOrderAddedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (orderBookPriority, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (legs, bytes) ← decodeUInt 1 bytes
  let (contractLegs_, bytes) ← decodeMany ContractLegs.decode 6 bytes
  if fits_contractLegs : contractLegs_.length = 6 then
    pure ({ nanoseconds, tradeDate, orderNumber, orderBookPriority, quantity, legs, contractLegs := ⟨contractLegs_, fits_contractLegs⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : CustomMarketOrderAddedMessage) : (encode message).length = 89 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const ContractLegs.encode 11 ContractLegs.encode_length, message.contractLegs.length_eq]

theorem encode_length_pos (message : CustomMarketOrderAddedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CustomMarketOrderAddedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeMany_exact 6 ContractLegs.encode ContractLegs.decode ContractLegs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.contractLegs.length_eq]
  rfl

end CustomMarketOrderAddedMessage

/-- Custom Market Order Replaced Message: 22 bytes -/
structure CustomMarketOrderReplacedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  orderNumber : BitVec 64
  orderBookPriority : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace CustomMarketOrderReplacedMessage

def encode (message : CustomMarketOrderReplacedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.orderBookPriority
    ++ (encodeUInt 4 message.quantity))))

def decode (bytes : List UInt8) : Option (CustomMarketOrderReplacedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (orderBookPriority, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, orderNumber, orderBookPriority, quantity }, bytes)

@[simp] theorem encode_length (message : CustomMarketOrderReplacedMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : CustomMarketOrderReplacedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CustomMarketOrderReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end CustomMarketOrderReplacedMessage

/-- Custom Market Order Deleted Message: 14 bytes -/
structure CustomMarketOrderDeletedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  orderNumber : BitVec 64
  deriving DecidableEq, Repr

namespace CustomMarketOrderDeletedMessage

def encode (message : CustomMarketOrderDeletedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 8 message.orderNumber))

def decode (bytes : List UInt8) : Option (CustomMarketOrderDeletedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, orderNumber }, bytes)

@[simp] theorem encode_length (message : CustomMarketOrderDeletedMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : CustomMarketOrderDeletedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CustomMarketOrderDeletedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CustomMarketOrderDeletedMessage

/-- Order Executed Message: 36 bytes -/
structure OrderExecutedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  side : Side
  orderNumber : BitVec 64
  quantityRemaining : BitVec 32
  tradeType : TradeType
  matchNumber : BitVec 32
  executedQuantity : BitVec 32
  tradePrice : BitVec 32
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.quantityRemaining
    ++ (TradeType.encode message.tradeType
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.tradePrice)))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (quantityRemaining, bytes) ← decodeUInt 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, side, orderNumber, quantityRemaining, tradeType, matchNumber, executedQuantity, tradePrice }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, TradeType.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Message: 47 bytes -/
structure OrderExecutedWithPriceMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  buyingOrderNumber : BitVec 64
  buyerQuantityRemaining : BitVec 32
  sellingOrderNumber : BitVec 64
  sellerQuantityRemaining : BitVec 32
  tradeType : TradeType
  matchNumber : BitVec 32
  executedQuantity : BitVec 32
  tradePrice : BitVec 32
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (encodeUInt 8 message.buyingOrderNumber
    ++ (encodeUInt 4 message.buyerQuantityRemaining
    ++ (encodeUInt 8 message.sellingOrderNumber
    ++ (encodeUInt 4 message.sellerQuantityRemaining
    ++ (TradeType.encode message.tradeType
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.tradePrice))))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (buyingOrderNumber, bytes) ← decodeUInt 8 bytes
  let (buyerQuantityRemaining, bytes) ← decodeUInt 4 bytes
  let (sellingOrderNumber, bytes) ← decodeUInt 8 bytes
  let (sellerQuantityRemaining, bytes) ← decodeUInt 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, buyingOrderNumber, buyerQuantityRemaining, sellingOrderNumber, sellerQuantityRemaining, tradeType, matchNumber, executedQuantity, tradePrice }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradeType.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedWithPriceMessage

/-- Spread Executed Message: 46 bytes -/
structure SpreadExecutedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  side : Side
  orderNumber : BitVec 64
  quantityRemaining : BitVec 32
  tradeType : TradeType
  matchNumber : BitVec 32
  executedQuantity : BitVec 32
  tradePrice : BitVec 32
  tradedContractNumber : BitVec 32
  spreadTradePrice : BitVec 32
  tradeSideOfLeg : Alpha 1
  printable : Printable
  deriving DecidableEq, Repr

namespace SpreadExecutedMessage

def encode (message : SpreadExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.quantityRemaining
    ++ (TradeType.encode message.tradeType
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.tradePrice
    ++ (encodeUInt 4 message.tradedContractNumber
    ++ (encodeUInt 4 message.spreadTradePrice
    ++ (Alpha.encode message.tradeSideOfLeg
    ++ (Printable.encode message.printable)))))))))))))

def decode (bytes : List UInt8) : Option (SpreadExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (quantityRemaining, bytes) ← decodeUInt 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (tradedContractNumber, bytes) ← decodeUInt 4 bytes
  let (spreadTradePrice, bytes) ← decodeUInt 4 bytes
  let (tradeSideOfLeg, bytes) ← Alpha.decode 1 bytes
  let (printable, bytes) ← Printable.decode bytes
  pure ({ nanoseconds, tradeDate, contractNumber, side, orderNumber, quantityRemaining, tradeType, matchNumber, executedQuantity, tradePrice, tradedContractNumber, spreadTradePrice, tradeSideOfLeg, printable }, bytes)

@[simp] theorem encode_length (message : SpreadExecutedMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, TradeType.encode_length, Alpha.encode_length, Printable.encode_length]

theorem encode_length_pos (message : SpreadExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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
  rw [Printable.decode_encode, some_bind]
  rfl

end SpreadExecutedMessage

/-- Trade Spread Execution Chain Message: 62 bytes -/
structure TradeSpreadExecutionChainMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  buyer : BitVec 32
  sideOfBuyer : Alpha 1
  buyerOrderNumber : BitVec 64
  buyerQuantityRemaining : BitVec 32
  sellerContractNumber : BitVec 32
  sideOfSeller : Alpha 1
  sellingOrderNumber : BitVec 64
  sellerQuantityRemaining : BitVec 32
  tradeType : TradeType
  matchNumber : BitVec 32
  executedQuantity : BitVec 32
  tradePrice : BitVec 32
  tradedContractNumber : BitVec 32
  spreadTradePrice : BitVec 32
  printable : Printable
  deriving DecidableEq, Repr

namespace TradeSpreadExecutionChainMessage

def encode (message : TradeSpreadExecutionChainMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.buyer
    ++ (Alpha.encode message.sideOfBuyer
    ++ (encodeUInt 8 message.buyerOrderNumber
    ++ (encodeUInt 4 message.buyerQuantityRemaining
    ++ (encodeUInt 4 message.sellerContractNumber
    ++ (Alpha.encode message.sideOfSeller
    ++ (encodeUInt 8 message.sellingOrderNumber
    ++ (encodeUInt 4 message.sellerQuantityRemaining
    ++ (TradeType.encode message.tradeType
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.tradePrice
    ++ (encodeUInt 4 message.tradedContractNumber
    ++ (encodeUInt 4 message.spreadTradePrice
    ++ (Printable.encode message.printable))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeSpreadExecutionChainMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (buyer, bytes) ← decodeUInt 4 bytes
  let (sideOfBuyer, bytes) ← Alpha.decode 1 bytes
  let (buyerOrderNumber, bytes) ← decodeUInt 8 bytes
  let (buyerQuantityRemaining, bytes) ← decodeUInt 4 bytes
  let (sellerContractNumber, bytes) ← decodeUInt 4 bytes
  let (sideOfSeller, bytes) ← Alpha.decode 1 bytes
  let (sellingOrderNumber, bytes) ← decodeUInt 8 bytes
  let (sellerQuantityRemaining, bytes) ← decodeUInt 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (tradedContractNumber, bytes) ← decodeUInt 4 bytes
  let (spreadTradePrice, bytes) ← decodeUInt 4 bytes
  let (printable, bytes) ← Printable.decode bytes
  pure ({ nanoseconds, tradeDate, buyer, sideOfBuyer, buyerOrderNumber, buyerQuantityRemaining, sellerContractNumber, sideOfSeller, sellingOrderNumber, sellerQuantityRemaining, tradeType, matchNumber, executedQuantity, tradePrice, tradedContractNumber, spreadTradePrice, printable }, bytes)

@[simp] theorem encode_length (message : TradeSpreadExecutionChainMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeType.encode_length, Printable.encode_length]

theorem encode_length_pos (message : TradeSpreadExecutionChainMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeSpreadExecutionChainMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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
  rw [Printable.decode_encode, some_bind]
  rfl

end TradeSpreadExecutionChainMessage

/-- Custom Market Executed Message: 37 bytes -/
structure CustomMarketExecutedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  orderNumber : BitVec 64
  quantityRemaining : BitVec 32
  tradeType : TradeType
  matchNumber : BitVec 32
  executedQuantity : BitVec 32
  tradePrice : BitVec 32
  tradedContractNumber : BitVec 32
  tradeSideOfLeg : Alpha 1
  printable : Printable
  deriving DecidableEq, Repr

namespace CustomMarketExecutedMessage

def encode (message : CustomMarketExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.quantityRemaining
    ++ (TradeType.encode message.tradeType
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.tradePrice
    ++ (encodeUInt 4 message.tradedContractNumber
    ++ (Alpha.encode message.tradeSideOfLeg
    ++ (Printable.encode message.printable))))))))))

def decode (bytes : List UInt8) : Option (CustomMarketExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (quantityRemaining, bytes) ← decodeUInt 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (tradedContractNumber, bytes) ← decodeUInt 4 bytes
  let (tradeSideOfLeg, bytes) ← Alpha.decode 1 bytes
  let (printable, bytes) ← Printable.decode bytes
  pure ({ nanoseconds, tradeDate, orderNumber, quantityRemaining, tradeType, matchNumber, executedQuantity, tradePrice, tradedContractNumber, tradeSideOfLeg, printable }, bytes)

@[simp] theorem encode_length (message : CustomMarketExecutedMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradeType.encode_length, Alpha.encode_length, Printable.encode_length]

theorem encode_length_pos (message : CustomMarketExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CustomMarketExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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
  rw [Printable.decode_encode, some_bind]
  rfl

end CustomMarketExecutedMessage

/-- Custom Market Trade Message: 54 bytes -/
structure CustomMarketTradeMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  side : Side
  orderNumber : BitVec 64
  quantityRemaining : BitVec 32
  customMarketOrderNumber : BitVec 64
  customMarketQuantityRemaining : BitVec 32
  tradeType : TradeType
  matchNumber : BitVec 32
  executedQuantity : BitVec 32
  tradePrice : BitVec 32
  tradedContractNumber : BitVec 32
  tradeSideOfNonCustomOrder : Alpha 1
  printable : Printable
  deriving DecidableEq, Repr

namespace CustomMarketTradeMessage

def encode (message : CustomMarketTradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.quantityRemaining
    ++ (encodeUInt 8 message.customMarketOrderNumber
    ++ (encodeUInt 4 message.customMarketQuantityRemaining
    ++ (TradeType.encode message.tradeType
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.tradePrice
    ++ (encodeUInt 4 message.tradedContractNumber
    ++ (Alpha.encode message.tradeSideOfNonCustomOrder
    ++ (Printable.encode message.printable))))))))))))))

def decode (bytes : List UInt8) : Option (CustomMarketTradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (quantityRemaining, bytes) ← decodeUInt 4 bytes
  let (customMarketOrderNumber, bytes) ← decodeUInt 8 bytes
  let (customMarketQuantityRemaining, bytes) ← decodeUInt 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (tradedContractNumber, bytes) ← decodeUInt 4 bytes
  let (tradeSideOfNonCustomOrder, bytes) ← Alpha.decode 1 bytes
  let (printable, bytes) ← Printable.decode bytes
  pure ({ nanoseconds, tradeDate, contractNumber, side, orderNumber, quantityRemaining, customMarketOrderNumber, customMarketQuantityRemaining, tradeType, matchNumber, executedQuantity, tradePrice, tradedContractNumber, tradeSideOfNonCustomOrder, printable }, bytes)

@[simp] theorem encode_length (message : CustomMarketTradeMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, TradeType.encode_length, Alpha.encode_length, Printable.encode_length]

theorem encode_length_pos (message : CustomMarketTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CustomMarketTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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
  rw [Printable.decode_encode, some_bind]
  rfl

end CustomMarketTradeMessage

/-- Trade Cancellation Message: 10 bytes -/
structure TradeCancellationMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  matchNumber : BitVec 32
  deriving DecidableEq, Repr

namespace TradeCancellationMessage

def encode (message : TradeCancellationMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.matchNumber))

def decode (bytes : List UInt8) : Option (TradeCancellationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, matchNumber }, bytes)

@[simp] theorem encode_length (message : TradeCancellationMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCancellationMessage

/-- Equilibrium Price Auction Info Message: 30 bytes -/
structure EquilibriumPriceAuctionInfoMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  equilibriumPrice : BitVec 32
  bestBidPrice : BitVec 32
  bestAskPrice : BitVec 32
  bestBidQuantity : BitVec 32
  bestAskQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace EquilibriumPriceAuctionInfoMessage

def encode (message : EquilibriumPriceAuctionInfoMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (encodeUInt 4 message.equilibriumPrice
    ++ (encodeUInt 4 message.bestBidPrice
    ++ (encodeUInt 4 message.bestAskPrice
    ++ (encodeUInt 4 message.bestBidQuantity
    ++ (encodeUInt 4 message.bestAskQuantity)))))))

def decode (bytes : List UInt8) : Option (EquilibriumPriceAuctionInfoMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (equilibriumPrice, bytes) ← decodeUInt 4 bytes
  let (bestBidPrice, bytes) ← decodeUInt 4 bytes
  let (bestAskPrice, bytes) ← decodeUInt 4 bytes
  let (bestBidQuantity, bytes) ← decodeUInt 4 bytes
  let (bestAskQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, equilibriumPrice, bestBidPrice, bestAskPrice, bestBidQuantity, bestAskQuantity }, bytes)

@[simp] theorem encode_length (message : EquilibriumPriceAuctionInfoMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : EquilibriumPriceAuctionInfoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquilibriumPriceAuctionInfoMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EquilibriumPriceAuctionInfoMessage

/-- Open High Low Last Trade Adjustment Message: 39 bytes -/
structure OpenHighLowLastTradeAdjustmentMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  openingTrade : BitVec 32
  highestTrade : BitVec 32
  lowestTrade : BitVec 32
  lastTrade : BitVec 32
  lastVolume : BitVec 32
  totalTradedVolume : BitVec 32
  totalTrades : BitVec 32
  marketUpdates : BitVec 8
  deriving DecidableEq, Repr

namespace OpenHighLowLastTradeAdjustmentMessage

def encode (message : OpenHighLowLastTradeAdjustmentMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (encodeUInt 4 message.openingTrade
    ++ (encodeUInt 4 message.highestTrade
    ++ (encodeUInt 4 message.lowestTrade
    ++ (encodeUInt 4 message.lastTrade
    ++ (encodeUInt 4 message.lastVolume
    ++ (encodeUInt 4 message.totalTradedVolume
    ++ (encodeUInt 4 message.totalTrades
    ++ (encodeUInt 1 message.marketUpdates))))))))))

def decode (bytes : List UInt8) : Option (OpenHighLowLastTradeAdjustmentMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (openingTrade, bytes) ← decodeUInt 4 bytes
  let (highestTrade, bytes) ← decodeUInt 4 bytes
  let (lowestTrade, bytes) ← decodeUInt 4 bytes
  let (lastTrade, bytes) ← decodeUInt 4 bytes
  let (lastVolume, bytes) ← decodeUInt 4 bytes
  let (totalTradedVolume, bytes) ← decodeUInt 4 bytes
  let (totalTrades, bytes) ← decodeUInt 4 bytes
  let (marketUpdates, bytes) ← decodeUInt 1 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, openingTrade, highestTrade, lowestTrade, lastTrade, lastVolume, totalTradedVolume, totalTrades, marketUpdates }, bytes)

@[simp] theorem encode_length (message : OpenHighLowLastTradeAdjustmentMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OpenHighLowLastTradeAdjustmentMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenHighLowLastTradeAdjustmentMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpenHighLowLastTradeAdjustmentMessage

/-- Market Settlement Message: 19 bytes -/
structure MarketSettlementMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  settlementPrice : BitVec 32
  volatility : BitVec 32
  settlementType : Alpha 1
  deriving DecidableEq, Repr

namespace MarketSettlementMessage

def encode (message : MarketSettlementMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (encodeUInt 4 message.settlementPrice
    ++ (encodeUInt 4 message.volatility
    ++ (Alpha.encode message.settlementType)))))

def decode (bytes : List UInt8) : Option (MarketSettlementMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (settlementPrice, bytes) ← decodeUInt 4 bytes
  let (volatility, bytes) ← decodeUInt 4 bytes
  let (settlementType, bytes) ← Alpha.decode 1 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, settlementPrice, volatility, settlementType }, bytes)

@[simp] theorem encode_length (message : MarketSettlementMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketSettlementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketSettlementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketSettlementMessage

/-- Ad Hoc Text Message: 112 bytes -/
structure AdHocTextMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  sourceId : Alpha 6
  textMessage : Alpha 100
  deriving DecidableEq, Repr

namespace AdHocTextMessage

def encode (message : AdHocTextMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (Alpha.encode message.sourceId
    ++ (Alpha.encode message.textMessage)))

def decode (bytes : List UInt8) : Option (AdHocTextMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (sourceId, bytes) ← Alpha.decode 6 bytes
  let (textMessage, bytes) ← Alpha.decode 100 bytes
  pure ({ nanoseconds, tradeDate, sourceId, textMessage }, bytes)

@[simp] theorem encode_length (message : AdHocTextMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : AdHocTextMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdHocTextMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AdHocTextMessage

/-- Request For Quote Message: 18 bytes -/
structure RequestForQuoteMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace RequestForQuoteMessage

def encode (message : RequestForQuoteMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.quantity))))

def decode (bytes : List UInt8) : Option (RequestForQuoteMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, price, quantity }, bytes)

@[simp] theorem encode_length (message : RequestForQuoteMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : RequestForQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestForQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end RequestForQuoteMessage

/-- Anomalous Order Threshold Publish Message: 34 bytes -/
structure AnomalousOrderThresholdPublishMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  aotPrice : BitVec 32
  aotUpperPrice : BitVec 32
  aotLowerPrice : BitVec 32
  etrPrice : BitVec 32
  etrUpperPrice : BitVec 32
  etrLowerPrice : BitVec 32
  deriving DecidableEq, Repr

namespace AnomalousOrderThresholdPublishMessage

def encode (message : AnomalousOrderThresholdPublishMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (encodeUInt 4 message.aotPrice
    ++ (encodeUInt 4 message.aotUpperPrice
    ++ (encodeUInt 4 message.aotLowerPrice
    ++ (encodeUInt 4 message.etrPrice
    ++ (encodeUInt 4 message.etrUpperPrice
    ++ (encodeUInt 4 message.etrLowerPrice))))))))

def decode (bytes : List UInt8) : Option (AnomalousOrderThresholdPublishMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (aotPrice, bytes) ← decodeUInt 4 bytes
  let (aotUpperPrice, bytes) ← decodeUInt 4 bytes
  let (aotLowerPrice, bytes) ← decodeUInt 4 bytes
  let (etrPrice, bytes) ← decodeUInt 4 bytes
  let (etrUpperPrice, bytes) ← decodeUInt 4 bytes
  let (etrLowerPrice, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, aotPrice, aotUpperPrice, aotLowerPrice, etrPrice, etrUpperPrice, etrLowerPrice }, bytes)

@[simp] theorem encode_length (message : AnomalousOrderThresholdPublishMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AnomalousOrderThresholdPublishMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AnomalousOrderThresholdPublishMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AnomalousOrderThresholdPublishMessage

/-- Volume And Open Interest Message: 20 bytes -/
structure VolumeAndOpenInterestMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  contractNumber : BitVec 32
  cumulativeVolume : BitVec 32
  openInterest : BitVec 32
  voiTradeDate : BitVec 16
  deriving DecidableEq, Repr

namespace VolumeAndOpenInterestMessage

def encode (message : VolumeAndOpenInterestMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.contractNumber
    ++ (encodeUInt 4 message.cumulativeVolume
    ++ (encodeUInt 4 message.openInterest
    ++ (encodeUInt 2 message.voiTradeDate)))))

def decode (bytes : List UInt8) : Option (VolumeAndOpenInterestMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (contractNumber, bytes) ← decodeUInt 4 bytes
  let (cumulativeVolume, bytes) ← decodeUInt 4 bytes
  let (openInterest, bytes) ← decodeUInt 4 bytes
  let (voiTradeDate, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, tradeDate, contractNumber, cumulativeVolume, openInterest, voiTradeDate }, bytes)

@[simp] theorem encode_length (message : VolumeAndOpenInterestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : VolumeAndOpenInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VolumeAndOpenInterestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end VolumeAndOpenInterestMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | timeMessage (message : TimeMessage) -- 'T' 0x54
  | systemEventMessage (message : SystemEventMessage) -- 'S' 0x53
  | futureSymbolDirectoryMessage (message : FutureSymbolDirectoryMessage) -- 'f' 0x66
  | spreadSymbolDirectoryMessage (message : SpreadSymbolDirectoryMessage) -- 'g' 0x67
  | optionSymbolDirectoryMessage (message : OptionSymbolDirectoryMessage) -- 'h' 0x68
  | orderBookStateMessage (message : OrderBookStateMessage) -- 'O' 0x4F
  | orderAddedMessage (message : OrderAddedMessage) -- 'A' 0x41
  | orderReplacedMessage (message : OrderReplacedMessage) -- 'U' 0x55
  | orderVolumeCancelledMessage (message : OrderVolumeCancelledMessage) -- 'X' 0x58
  | orderDeletedMessage (message : OrderDeletedMessage) -- 'D' 0x44
  | impliedOrderAddedMessage (message : ImpliedOrderAddedMessage) -- 'j' 0x6A
  | impliedOrderReplacedMessage (message : ImpliedOrderReplacedMessage) -- 'l' 0x6C
  | impliedOrderDeletedMessage (message : ImpliedOrderDeletedMessage) -- 'k' 0x6B
  | customMarketOrderAddedMessage (message : CustomMarketOrderAddedMessage) -- 'm' 0x6D
  | customMarketOrderReplacedMessage (message : CustomMarketOrderReplacedMessage) -- 'n' 0x6E
  | customMarketOrderDeletedMessage (message : CustomMarketOrderDeletedMessage) -- 'r' 0x72
  | orderExecutedMessage (message : OrderExecutedMessage) -- 'E' 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- 'C' 0x43
  | spreadExecutedMessage (message : SpreadExecutedMessage) -- 'e' 0x65
  | tradeSpreadExecutionChainMessage (message : TradeSpreadExecutionChainMessage) -- 'P' 0x50
  | customMarketExecutedMessage (message : CustomMarketExecutedMessage) -- 'u' 0x75
  | customMarketTradeMessage (message : CustomMarketTradeMessage) -- 'p' 0x70
  | tradeCancellationMessage (message : TradeCancellationMessage) -- 'B' 0x42
  | equilibriumPriceAuctionInfoMessage (message : EquilibriumPriceAuctionInfoMessage) -- 'Z' 0x5A
  | openHighLowLastTradeAdjustmentMessage (message : OpenHighLowLastTradeAdjustmentMessage) -- 't' 0x74
  | marketSettlementMessage (message : MarketSettlementMessage) -- 'Y' 0x59
  | adHocTextMessage (message : AdHocTextMessage) -- 'x' 0x78
  | requestForQuoteMessage (message : RequestForQuoteMessage) -- 'q' 0x71
  | anomalousOrderThresholdPublishMessage (message : AnomalousOrderThresholdPublishMessage) -- 'W' 0x57
  | volumeAndOpenInterestMessage (message : VolumeAndOpenInterestMessage) -- 'V' 0x56
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .timeMessage _ => 84
  | .systemEventMessage _ => 83
  | .futureSymbolDirectoryMessage _ => 102
  | .spreadSymbolDirectoryMessage _ => 103
  | .optionSymbolDirectoryMessage _ => 104
  | .orderBookStateMessage _ => 79
  | .orderAddedMessage _ => 65
  | .orderReplacedMessage _ => 85
  | .orderVolumeCancelledMessage _ => 88
  | .orderDeletedMessage _ => 68
  | .impliedOrderAddedMessage _ => 106
  | .impliedOrderReplacedMessage _ => 108
  | .impliedOrderDeletedMessage _ => 107
  | .customMarketOrderAddedMessage _ => 109
  | .customMarketOrderReplacedMessage _ => 110
  | .customMarketOrderDeletedMessage _ => 114
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .spreadExecutedMessage _ => 101
  | .tradeSpreadExecutionChainMessage _ => 80
  | .customMarketExecutedMessage _ => 117
  | .customMarketTradeMessage _ => 112
  | .tradeCancellationMessage _ => 66
  | .equilibriumPriceAuctionInfoMessage _ => 90
  | .openHighLowLastTradeAdjustmentMessage _ => 116
  | .marketSettlementMessage _ => 89
  | .adHocTextMessage _ => 120
  | .requestForQuoteMessage _ => 113
  | .anomalousOrderThresholdPublishMessage _ => 87
  | .volumeAndOpenInterestMessage _ => 86

def encode : Payload → List UInt8
  | .timeMessage message => TimeMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .futureSymbolDirectoryMessage message => FutureSymbolDirectoryMessage.encode message
  | .spreadSymbolDirectoryMessage message => SpreadSymbolDirectoryMessage.encode message
  | .optionSymbolDirectoryMessage message => OptionSymbolDirectoryMessage.encode message
  | .orderBookStateMessage message => OrderBookStateMessage.encode message
  | .orderAddedMessage message => OrderAddedMessage.encode message
  | .orderReplacedMessage message => OrderReplacedMessage.encode message
  | .orderVolumeCancelledMessage message => OrderVolumeCancelledMessage.encode message
  | .orderDeletedMessage message => OrderDeletedMessage.encode message
  | .impliedOrderAddedMessage message => ImpliedOrderAddedMessage.encode message
  | .impliedOrderReplacedMessage message => ImpliedOrderReplacedMessage.encode message
  | .impliedOrderDeletedMessage message => ImpliedOrderDeletedMessage.encode message
  | .customMarketOrderAddedMessage message => CustomMarketOrderAddedMessage.encode message
  | .customMarketOrderReplacedMessage message => CustomMarketOrderReplacedMessage.encode message
  | .customMarketOrderDeletedMessage message => CustomMarketOrderDeletedMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .spreadExecutedMessage message => SpreadExecutedMessage.encode message
  | .tradeSpreadExecutionChainMessage message => TradeSpreadExecutionChainMessage.encode message
  | .customMarketExecutedMessage message => CustomMarketExecutedMessage.encode message
  | .customMarketTradeMessage message => CustomMarketTradeMessage.encode message
  | .tradeCancellationMessage message => TradeCancellationMessage.encode message
  | .equilibriumPriceAuctionInfoMessage message => EquilibriumPriceAuctionInfoMessage.encode message
  | .openHighLowLastTradeAdjustmentMessage message => OpenHighLowLastTradeAdjustmentMessage.encode message
  | .marketSettlementMessage message => MarketSettlementMessage.encode message
  | .adHocTextMessage message => AdHocTextMessage.encode message
  | .requestForQuoteMessage message => RequestForQuoteMessage.encode message
  | .anomalousOrderThresholdPublishMessage message => AnomalousOrderThresholdPublishMessage.encode message
  | .volumeAndOpenInterestMessage message => VolumeAndOpenInterestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 112 := by
  cases message with
  | timeMessage inner =>
    simp only [encode, TimeMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | futureSymbolDirectoryMessage inner =>
    simp only [encode, FutureSymbolDirectoryMessage.encode_length]
    omega
  | spreadSymbolDirectoryMessage inner =>
    simp only [encode, SpreadSymbolDirectoryMessage.encode_length]
    omega
  | optionSymbolDirectoryMessage inner =>
    simp only [encode, OptionSymbolDirectoryMessage.encode_length]
    omega
  | orderBookStateMessage inner =>
    simp only [encode, OrderBookStateMessage.encode_length]
    omega
  | orderAddedMessage inner =>
    simp only [encode, OrderAddedMessage.encode_length]
    omega
  | orderReplacedMessage inner =>
    simp only [encode, OrderReplacedMessage.encode_length]
    omega
  | orderVolumeCancelledMessage inner =>
    simp only [encode, OrderVolumeCancelledMessage.encode_length]
    omega
  | orderDeletedMessage inner =>
    simp only [encode, OrderDeletedMessage.encode_length]
    omega
  | impliedOrderAddedMessage inner =>
    simp only [encode, ImpliedOrderAddedMessage.encode_length]
    omega
  | impliedOrderReplacedMessage inner =>
    simp only [encode, ImpliedOrderReplacedMessage.encode_length]
    omega
  | impliedOrderDeletedMessage inner =>
    simp only [encode, ImpliedOrderDeletedMessage.encode_length]
    omega
  | customMarketOrderAddedMessage inner =>
    simp only [encode, CustomMarketOrderAddedMessage.encode_length]
    omega
  | customMarketOrderReplacedMessage inner =>
    simp only [encode, CustomMarketOrderReplacedMessage.encode_length]
    omega
  | customMarketOrderDeletedMessage inner =>
    simp only [encode, CustomMarketOrderDeletedMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [encode, OrderExecutedWithPriceMessage.encode_length]
    omega
  | spreadExecutedMessage inner =>
    simp only [encode, SpreadExecutedMessage.encode_length]
    omega
  | tradeSpreadExecutionChainMessage inner =>
    simp only [encode, TradeSpreadExecutionChainMessage.encode_length]
    omega
  | customMarketExecutedMessage inner =>
    simp only [encode, CustomMarketExecutedMessage.encode_length]
    omega
  | customMarketTradeMessage inner =>
    simp only [encode, CustomMarketTradeMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [encode, TradeCancellationMessage.encode_length]
    omega
  | equilibriumPriceAuctionInfoMessage inner =>
    simp only [encode, EquilibriumPriceAuctionInfoMessage.encode_length]
    omega
  | openHighLowLastTradeAdjustmentMessage inner =>
    simp only [encode, OpenHighLowLastTradeAdjustmentMessage.encode_length]
    omega
  | marketSettlementMessage inner =>
    simp only [encode, MarketSettlementMessage.encode_length]
    omega
  | adHocTextMessage inner =>
    simp only [encode, AdHocTextMessage.encode_length]
    omega
  | requestForQuoteMessage inner =>
    simp only [encode, RequestForQuoteMessage.encode_length]
    omega
  | anomalousOrderThresholdPublishMessage inner =>
    simp only [encode, AnomalousOrderThresholdPublishMessage.encode_length]
    omega
  | volumeAndOpenInterestMessage inner =>
    simp only [encode, VolumeAndOpenInterestMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (TimeMessage.decode bytes).map fun (message, rest) => (.timeMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 102 then (FutureSymbolDirectoryMessage.decode bytes).map fun (message, rest) => (.futureSymbolDirectoryMessage message, rest)
  else if tag = 103 then (SpreadSymbolDirectoryMessage.decode bytes).map fun (message, rest) => (.spreadSymbolDirectoryMessage message, rest)
  else if tag = 104 then (OptionSymbolDirectoryMessage.decode bytes).map fun (message, rest) => (.optionSymbolDirectoryMessage message, rest)
  else if tag = 79 then (OrderBookStateMessage.decode bytes).map fun (message, rest) => (.orderBookStateMessage message, rest)
  else if tag = 65 then (OrderAddedMessage.decode bytes).map fun (message, rest) => (.orderAddedMessage message, rest)
  else if tag = 85 then (OrderReplacedMessage.decode bytes).map fun (message, rest) => (.orderReplacedMessage message, rest)
  else if tag = 88 then (OrderVolumeCancelledMessage.decode bytes).map fun (message, rest) => (.orderVolumeCancelledMessage message, rest)
  else if tag = 68 then (OrderDeletedMessage.decode bytes).map fun (message, rest) => (.orderDeletedMessage message, rest)
  else if tag = 106 then (ImpliedOrderAddedMessage.decode bytes).map fun (message, rest) => (.impliedOrderAddedMessage message, rest)
  else if tag = 108 then (ImpliedOrderReplacedMessage.decode bytes).map fun (message, rest) => (.impliedOrderReplacedMessage message, rest)
  else if tag = 107 then (ImpliedOrderDeletedMessage.decode bytes).map fun (message, rest) => (.impliedOrderDeletedMessage message, rest)
  else if tag = 109 then (CustomMarketOrderAddedMessage.decode bytes).map fun (message, rest) => (.customMarketOrderAddedMessage message, rest)
  else if tag = 110 then (CustomMarketOrderReplacedMessage.decode bytes).map fun (message, rest) => (.customMarketOrderReplacedMessage message, rest)
  else if tag = 114 then (CustomMarketOrderDeletedMessage.decode bytes).map fun (message, rest) => (.customMarketOrderDeletedMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 101 then (SpreadExecutedMessage.decode bytes).map fun (message, rest) => (.spreadExecutedMessage message, rest)
  else if tag = 80 then (TradeSpreadExecutionChainMessage.decode bytes).map fun (message, rest) => (.tradeSpreadExecutionChainMessage message, rest)
  else if tag = 117 then (CustomMarketExecutedMessage.decode bytes).map fun (message, rest) => (.customMarketExecutedMessage message, rest)
  else if tag = 112 then (CustomMarketTradeMessage.decode bytes).map fun (message, rest) => (.customMarketTradeMessage message, rest)
  else if tag = 66 then (TradeCancellationMessage.decode bytes).map fun (message, rest) => (.tradeCancellationMessage message, rest)
  else if tag = 90 then (EquilibriumPriceAuctionInfoMessage.decode bytes).map fun (message, rest) => (.equilibriumPriceAuctionInfoMessage message, rest)
  else if tag = 116 then (OpenHighLowLastTradeAdjustmentMessage.decode bytes).map fun (message, rest) => (.openHighLowLastTradeAdjustmentMessage message, rest)
  else if tag = 89 then (MarketSettlementMessage.decode bytes).map fun (message, rest) => (.marketSettlementMessage message, rest)
  else if tag = 120 then (AdHocTextMessage.decode bytes).map fun (message, rest) => (.adHocTextMessage message, rest)
  else if tag = 113 then (RequestForQuoteMessage.decode bytes).map fun (message, rest) => (.requestForQuoteMessage message, rest)
  else if tag = 87 then (AnomalousOrderThresholdPublishMessage.decode bytes).map fun (message, rest) => (.anomalousOrderThresholdPublishMessage message, rest)
  else if tag = 86 then (VolumeAndOpenInterestMessage.decode bytes).map fun (message, rest) => (.volumeAndOpenInterestMessage message, rest)
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
  | timeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TimeMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | futureSymbolDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, FutureSymbolDirectoryMessage.encode_length]
    omega
  | spreadSymbolDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SpreadSymbolDirectoryMessage.encode_length]
    omega
  | optionSymbolDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OptionSymbolDirectoryMessage.encode_length]
    omega
  | orderBookStateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookStateMessage.encode_length]
    omega
  | orderAddedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderAddedMessage.encode_length]
    omega
  | orderReplacedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderReplacedMessage.encode_length]
    omega
  | orderVolumeCancelledMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderVolumeCancelledMessage.encode_length]
    omega
  | orderDeletedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeletedMessage.encode_length]
    omega
  | impliedOrderAddedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ImpliedOrderAddedMessage.encode_length]
    omega
  | impliedOrderReplacedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ImpliedOrderReplacedMessage.encode_length]
    omega
  | impliedOrderDeletedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ImpliedOrderDeletedMessage.encode_length]
    omega
  | customMarketOrderAddedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CustomMarketOrderAddedMessage.encode_length]
    omega
  | customMarketOrderReplacedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CustomMarketOrderReplacedMessage.encode_length]
    omega
  | customMarketOrderDeletedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CustomMarketOrderDeletedMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | spreadExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SpreadExecutedMessage.encode_length]
    omega
  | tradeSpreadExecutionChainMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeSpreadExecutionChainMessage.encode_length]
    omega
  | customMarketExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CustomMarketExecutedMessage.encode_length]
    omega
  | customMarketTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CustomMarketTradeMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeCancellationMessage.encode_length]
    omega
  | equilibriumPriceAuctionInfoMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquilibriumPriceAuctionInfoMessage.encode_length]
    omega
  | openHighLowLastTradeAdjustmentMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OpenHighLowLastTradeAdjustmentMessage.encode_length]
    omega
  | marketSettlementMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketSettlementMessage.encode_length]
    omega
  | adHocTextMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AdHocTextMessage.encode_length]
    omega
  | requestForQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RequestForQuoteMessage.encode_length]
    omega
  | anomalousOrderThresholdPublishMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AnomalousOrderThresholdPublishMessage.encode_length]
    omega
  | volumeAndOpenInterestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, VolumeAndOpenInterestMessage.encode_length]
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
  session : Session
  sequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Session.encode message.session
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Session.decode bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Session.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Session.decode_encode, some_bind]
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

end Omi.AsxAsxderivativesT24ItchV113
