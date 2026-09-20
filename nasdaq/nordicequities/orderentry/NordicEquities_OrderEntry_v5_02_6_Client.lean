import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Nordic Ouch 5 Order Entry v5.02.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Party Role Qualifier is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Unsequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Note: Client Soup Bin Tcp Packet's Packet Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNordicequitiesOrderentryOuchV5026Client

/-- Buy Sell Indicator: one byte code -/
def BuySellIndicator.codes : List UInt8 :=
  [0x42, 0x53]

inductive BuySellIndicator where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySellIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySellIndicator :=
  if byte = 0x42 then .buyOrder
  else .sellOrder

def ofByte (byte : UInt8) : BuySellIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySellIndicator) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuySellIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuySellIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuySellIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BuySellIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuySellIndicator

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x36, 0x37, 0x38, 0x39]

inductive Capacity where
  | client -- Client
  | ownAccount -- Own Account
  | marketMaker -- Market Maker
  | issuerHolding -- Issuer Holding
  | issuePriceStabilizing -- Issue Price Stabilizing
  | risklessPrincipal -- Riskless Principal
  | issuerHoldingDeal -- Issuer Holding Deal
  | issuePriceStabilizingDeal -- Issue Price Stabilizing Deal
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .client => 0x31
  | .ownAccount => 0x32
  | .marketMaker => 0x33
  | .issuerHolding => 0x34
  | .issuePriceStabilizing => 0x36
  | .risklessPrincipal => 0x37
  | .issuerHoldingDeal => 0x38
  | .issuePriceStabilizingDeal => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x31 then .client
  else if byte = 0x32 then .ownAccount
  else if byte = 0x33 then .marketMaker
  else if byte = 0x34 then .issuerHolding
  else if byte = 0x36 then .issuePriceStabilizing
  else if byte = 0x37 then .risklessPrincipal
  else if byte = 0x38 then .issuerHoldingDeal
  else .issuePriceStabilizingDeal

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | client => decide
  | ownAccount => decide
  | marketMaker => decide
  | issuerHolding => decide
  | issuePriceStabilizing => decide
  | risklessPrincipal => decide
  | issuerHoldingDeal => decide
  | issuePriceStabilizingDeal => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Capacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Capacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Capacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Capacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Capacity

/-- Algo Indicator: one byte code -/
def AlgoIndicator.codes : List UInt8 :=
  [0x2D, 0x48]

inductive AlgoIndicator where
  | noAlgo -- No Algo
  | algo -- Algo
  | unlisted (byte : { byte : UInt8 // byte ∉ AlgoIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AlgoIndicator

def toByte : AlgoIndicator → UInt8
  | .noAlgo => 0x2D
  | .algo => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AlgoIndicator :=
  if byte = 0x2D then .noAlgo
  else .algo

def ofByte (byte : UInt8) : AlgoIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AlgoIndicator) : ofByte value.toByte = value := by
  cases value with
  | noAlgo => decide
  | algo => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AlgoIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AlgoIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AlgoIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AlgoIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AlgoIndicator

/-- Clearing Account Type Value: one byte code -/
def ClearingAccountTypeValue.codes : List UInt8 :=
  [0x31, 0x32]

inductive ClearingAccountTypeValue where
  | customerClient -- Customer Client
  | firmHouse -- Firm House
  | unlisted (byte : { byte : UInt8 // byte ∉ ClearingAccountTypeValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClearingAccountTypeValue

def toByte : ClearingAccountTypeValue → UInt8
  | .customerClient => 0x31
  | .firmHouse => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClearingAccountTypeValue :=
  if byte = 0x31 then .customerClient
  else .firmHouse

def ofByte (byte : UInt8) : ClearingAccountTypeValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClearingAccountTypeValue) : ofByte value.toByte = value := by
  cases value with
  | customerClient => decide
  | firmHouse => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClearingAccountTypeValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClearingAccountTypeValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClearingAccountTypeValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ClearingAccountTypeValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClearingAccountTypeValue

/-- Cross Type Value: one byte code -/
def CrossTypeValue.codes : List UInt8 :=
  [0x43, 0x4F, 0x49, 0x48, 0x41]

inductive CrossTypeValue where
  | closingCross -- Closing Cross
  | openingCross -- Opening Cross
  | scheduledIntradayCross -- Scheduled Intraday Cross
  | haltCross -- Halt Cross
  | auctionOnDemand -- Auction On Demand
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossTypeValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossTypeValue

def toByte : CrossTypeValue → UInt8
  | .closingCross => 0x43
  | .openingCross => 0x4F
  | .scheduledIntradayCross => 0x49
  | .haltCross => 0x48
  | .auctionOnDemand => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossTypeValue :=
  if byte = 0x43 then .closingCross
  else if byte = 0x4F then .openingCross
  else if byte = 0x49 then .scheduledIntradayCross
  else if byte = 0x48 then .haltCross
  else .auctionOnDemand

def ofByte (byte : UInt8) : CrossTypeValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossTypeValue) : ofByte value.toByte = value := by
  cases value with
  | closingCross => decide
  | openingCross => decide
  | scheduledIntradayCross => decide
  | haltCross => decide
  | auctionOnDemand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossTypeValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossTypeValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossTypeValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CrossTypeValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossTypeValue

/-- Dea Indicator Value: one byte code -/
def DeaIndicatorValue.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35]

inductive DeaIndicatorValue where
  | orderReceivedFromACustomer -- Order Received From A Customer
  | orderReceivedFromWithinTheFirm -- Order Received From Within The Firm
  | orderReceivedFromAnotherBrokerDealer -- Order Received From Another Broker Dealer
  | orderReceivedFromACustomerOrOriginatedWithTheFirm -- Order Received From A Customer Or Originated With The Firm
  | orderReceivedFromADirectAccessOrSponsoredAccessCustomer -- Order Received From A Direct Access Or Sponsored Access Customer
  | unlisted (byte : { byte : UInt8 // byte ∉ DeaIndicatorValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeaIndicatorValue

def toByte : DeaIndicatorValue → UInt8
  | .orderReceivedFromACustomer => 0x31
  | .orderReceivedFromWithinTheFirm => 0x32
  | .orderReceivedFromAnotherBrokerDealer => 0x33
  | .orderReceivedFromACustomerOrOriginatedWithTheFirm => 0x34
  | .orderReceivedFromADirectAccessOrSponsoredAccessCustomer => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeaIndicatorValue :=
  if byte = 0x31 then .orderReceivedFromACustomer
  else if byte = 0x32 then .orderReceivedFromWithinTheFirm
  else if byte = 0x33 then .orderReceivedFromAnotherBrokerDealer
  else if byte = 0x34 then .orderReceivedFromACustomerOrOriginatedWithTheFirm
  else .orderReceivedFromADirectAccessOrSponsoredAccessCustomer

def ofByte (byte : UInt8) : DeaIndicatorValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeaIndicatorValue) : ofByte value.toByte = value := by
  cases value with
  | orderReceivedFromACustomer => decide
  | orderReceivedFromWithinTheFirm => decide
  | orderReceivedFromAnotherBrokerDealer => decide
  | orderReceivedFromACustomerOrOriginatedWithTheFirm => decide
  | orderReceivedFromADirectAccessOrSponsoredAccessCustomer => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeaIndicatorValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeaIndicatorValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeaIndicatorValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DeaIndicatorValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeaIndicatorValue

/-- Display Value: one byte code -/
def DisplayValue.codes : List UInt8 :=
  [0x59, 0x4E, 0x41, 0x4D, 0x53]

inductive DisplayValue where
  | display -- Display
  | nonDisplay -- Non Display
  | auctionOnDemand -- Auction On Demand
  | nordicMid -- Nordic Mid
  | pureStream -- Pure Stream
  | unlisted (byte : { byte : UInt8 // byte ∉ DisplayValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DisplayValue

def toByte : DisplayValue → UInt8
  | .display => 0x59
  | .nonDisplay => 0x4E
  | .auctionOnDemand => 0x41
  | .nordicMid => 0x4D
  | .pureStream => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DisplayValue :=
  if byte = 0x59 then .display
  else if byte = 0x4E then .nonDisplay
  else if byte = 0x41 then .auctionOnDemand
  else if byte = 0x4D then .nordicMid
  else .pureStream

def ofByte (byte : UInt8) : DisplayValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DisplayValue) : ofByte value.toByte = value := by
  cases value with
  | display => decide
  | nonDisplay => decide
  | auctionOnDemand => decide
  | nordicMid => decide
  | pureStream => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DisplayValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DisplayValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DisplayValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DisplayValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DisplayValue

/-- Liquidity Provision Indicator Value: one byte code -/
def LiquidityProvisionIndicatorValue.codes : List UInt8 :=
  [0x4E, 0x59]

inductive LiquidityProvisionIndicatorValue where
  | noLiquidityProvision -- No Liquidity Provision
  | liquidityProvision -- Liquidity Provision
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityProvisionIndicatorValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityProvisionIndicatorValue

def toByte : LiquidityProvisionIndicatorValue → UInt8
  | .noLiquidityProvision => 0x4E
  | .liquidityProvision => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityProvisionIndicatorValue :=
  if byte = 0x4E then .noLiquidityProvision
  else .liquidityProvision

def ofByte (byte : UInt8) : LiquidityProvisionIndicatorValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityProvisionIndicatorValue) : ofByte value.toByte = value := by
  cases value with
  | noLiquidityProvision => decide
  | liquidityProvision => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityProvisionIndicatorValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityProvisionIndicatorValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityProvisionIndicatorValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LiquidityProvisionIndicatorValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityProvisionIndicatorValue

/-- Peg Type Value: one byte code -/
def PegTypeValue.codes : List UInt8 :=
  [0x4D, 0x50, 0x52]

inductive PegTypeValue where
  | midpoint -- Midpoint
  | market -- Market
  | primary -- Primary
  | unlisted (byte : { byte : UInt8 // byte ∉ PegTypeValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PegTypeValue

def toByte : PegTypeValue → UInt8
  | .midpoint => 0x4D
  | .market => 0x50
  | .primary => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PegTypeValue :=
  if byte = 0x4D then .midpoint
  else if byte = 0x50 then .market
  else .primary

def ofByte (byte : UInt8) : PegTypeValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PegTypeValue) : ofByte value.toByte = value := by
  cases value with
  | midpoint => decide
  | market => decide
  | primary => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PegTypeValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PegTypeValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PegTypeValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PegTypeValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PegTypeValue

/-- Stp Action Value: one byte code -/
def StpActionValue.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34]

inductive StpActionValue where
  | cancelPassiveOrder -- Cancel Passive Order
  | cancelAggressiveOrder -- Cancel Aggressive Order
  | cancelBothOrders -- Cancel Both Orders
  | createATransferTransaction -- Create A Transfer Transaction
  | unlisted (byte : { byte : UInt8 // byte ∉ StpActionValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StpActionValue

def toByte : StpActionValue → UInt8
  | .cancelPassiveOrder => 0x31
  | .cancelAggressiveOrder => 0x32
  | .cancelBothOrders => 0x33
  | .createATransferTransaction => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StpActionValue :=
  if byte = 0x31 then .cancelPassiveOrder
  else if byte = 0x32 then .cancelAggressiveOrder
  else if byte = 0x33 then .cancelBothOrders
  else .createATransferTransaction

def ofByte (byte : UInt8) : StpActionValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StpActionValue) : ofByte value.toByte = value := by
  cases value with
  | cancelPassiveOrder => decide
  | cancelAggressiveOrder => decide
  | cancelBothOrders => decide
  | createATransferTransaction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StpActionValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StpActionValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StpActionValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StpActionValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StpActionValue

/-- Stp Level Value: one byte code -/
def StpLevelValue.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive StpLevelValue where
  | mpidAndTrader -- Mpid And Trader
  | mpid -- Mpid
  | specifiedTraderGroup -- Specified Trader Group
  | unlisted (byte : { byte : UInt8 // byte ∉ StpLevelValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StpLevelValue

def toByte : StpLevelValue → UInt8
  | .mpidAndTrader => 0x31
  | .mpid => 0x32
  | .specifiedTraderGroup => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StpLevelValue :=
  if byte = 0x31 then .mpidAndTrader
  else if byte = 0x32 then .mpid
  else .specifiedTraderGroup

def ofByte (byte : UInt8) : StpLevelValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StpLevelValue) : ofByte value.toByte = value := by
  cases value with
  | mpidAndTrader => decide
  | mpid => decide
  | specifiedTraderGroup => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StpLevelValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StpLevelValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StpLevelValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StpLevelValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StpLevelValue

/-- Time In Force Value: one byte code -/
def TimeInForceValue.codes : List UInt8 :=
  [0x30, 0x31, 0x33, 0x36, 0x42]

inductive TimeInForceValue where
  | day -- Day
  | gtcGoodTillCancelled -- Gtc Good Till Cancelled
  | iocImmediateOrCancel -- Ioc Immediate Or Cancel
  | gttGoodTillTime -- Gtt Good Till Time
  | gfaGoodForAuction -- Gfa Good For Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForceValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForceValue

def toByte : TimeInForceValue → UInt8
  | .day => 0x30
  | .gtcGoodTillCancelled => 0x31
  | .iocImmediateOrCancel => 0x33
  | .gttGoodTillTime => 0x36
  | .gfaGoodForAuction => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForceValue :=
  if byte = 0x30 then .day
  else if byte = 0x31 then .gtcGoodTillCancelled
  else if byte = 0x33 then .iocImmediateOrCancel
  else if byte = 0x36 then .gttGoodTillTime
  else .gfaGoodForAuction

def ofByte (byte : UInt8) : TimeInForceValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForceValue) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | gtcGoodTillCancelled => decide
  | iocImmediateOrCancel => decide
  | gttGoodTillTime => decide
  | gfaGoodForAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForceValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForceValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForceValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TimeInForceValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForceValue

/-- Trading At Closing Price Value: one byte code -/
def TradingAtClosingPriceValue.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TradingAtClosingPriceValue where
  | participateInTradingAtClosingPrice -- Participate In Trading At Closing Price
  | doNotParticipateInTradingAtClosingPrice -- Do Not Participate In Trading At Closing Price
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingAtClosingPriceValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingAtClosingPriceValue

def toByte : TradingAtClosingPriceValue → UInt8
  | .participateInTradingAtClosingPrice => 0x59
  | .doNotParticipateInTradingAtClosingPrice => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingAtClosingPriceValue :=
  if byte = 0x59 then .participateInTradingAtClosingPrice
  else .doNotParticipateInTradingAtClosingPrice

def ofByte (byte : UInt8) : TradingAtClosingPriceValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingAtClosingPriceValue) : ofByte value.toByte = value := by
  cases value with
  | participateInTradingAtClosingPrice => decide
  | doNotParticipateInTradingAtClosingPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingAtClosingPriceValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingAtClosingPriceValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingAtClosingPriceValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingAtClosingPriceValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingAtClosingPriceValue

/-- Order Condition Value: one byte code -/
def OrderConditionValue.codes : List UInt8 :=
  [0x57, 0x55, 0x50, 0x51, 0x54]

inductive OrderConditionValue where
  | marketMakerOrder -- Market Maker Order
  | marketMakerOrderRefresh -- Market Maker Order Refresh
  | topofBook -- Topof Book
  | darklitSweep -- Darklit Sweep
  | tradeNow -- Trade Now
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderConditionValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderConditionValue

def toByte : OrderConditionValue → UInt8
  | .marketMakerOrder => 0x57
  | .marketMakerOrderRefresh => 0x55
  | .topofBook => 0x50
  | .darklitSweep => 0x51
  | .tradeNow => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderConditionValue :=
  if byte = 0x57 then .marketMakerOrder
  else if byte = 0x55 then .marketMakerOrderRefresh
  else if byte = 0x50 then .topofBook
  else if byte = 0x51 then .darklitSweep
  else .tradeNow

def ofByte (byte : UInt8) : OrderConditionValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderConditionValue) : ofByte value.toByte = value := by
  cases value with
  | marketMakerOrder => decide
  | marketMakerOrderRefresh => decide
  | topofBook => decide
  | darklitSweep => decide
  | tradeNow => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderConditionValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderConditionValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderConditionValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderConditionValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderConditionValue

/-- Customer Order Capacity Value: one byte code -/
def CustomerOrderCapacityValue.codes : List UInt8 :=
  [0x35]

inductive CustomerOrderCapacityValue where
  | retailCustomer -- Retail Customer
  | unlisted (byte : { byte : UInt8 // byte ∉ CustomerOrderCapacityValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustomerOrderCapacityValue

def toByte : CustomerOrderCapacityValue → UInt8
  | .retailCustomer => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : CustomerOrderCapacityValue :=
  .retailCustomer

def ofByte (byte : UInt8) : CustomerOrderCapacityValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustomerOrderCapacityValue) : ofByte value.toByte = value := by
  cases value with
  | retailCustomer => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CustomerOrderCapacityValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CustomerOrderCapacityValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CustomerOrderCapacityValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CustomerOrderCapacityValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CustomerOrderCapacityValue

/-- Target Strategy Value: one byte code -/
def TargetStrategyValue.codes : List UInt8 :=
  [0x30, 0x31, 0x35, 0x43]

inductive TargetStrategyValue where
  | rate5To15Percent -- Rate 5 To 15 Percent
  | rate5To30Percent -- Rate 5 To 30 Percent
  | rate10To200Percent -- Rate 10 To 200 Percent
  | custom -- Custom
  | unlisted (byte : { byte : UInt8 // byte ∉ TargetStrategyValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TargetStrategyValue

def toByte : TargetStrategyValue → UInt8
  | .rate5To15Percent => 0x30
  | .rate5To30Percent => 0x31
  | .rate10To200Percent => 0x35
  | .custom => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TargetStrategyValue :=
  if byte = 0x30 then .rate5To15Percent
  else if byte = 0x31 then .rate5To30Percent
  else if byte = 0x35 then .rate10To200Percent
  else .custom

def ofByte (byte : UInt8) : TargetStrategyValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TargetStrategyValue) : ofByte value.toByte = value := by
  cases value with
  | rate5To15Percent => decide
  | rate5To30Percent => decide
  | rate10To200Percent => decide
  | custom => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TargetStrategyValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TargetStrategyValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TargetStrategyValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TargetStrategyValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TargetStrategyValue

/-- Conditional Type Value: one byte code -/
def ConditionalTypeValue.codes : List UInt8 :=
  [0x43, 0x46]

inductive ConditionalTypeValue where
  | conditionalOrder -- Conditional Order
  | firmUpOrder -- Firm Up Order
  | unlisted (byte : { byte : UInt8 // byte ∉ ConditionalTypeValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ConditionalTypeValue

def toByte : ConditionalTypeValue → UInt8
  | .conditionalOrder => 0x43
  | .firmUpOrder => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ConditionalTypeValue :=
  if byte = 0x43 then .conditionalOrder
  else .firmUpOrder

def ofByte (byte : UInt8) : ConditionalTypeValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ConditionalTypeValue) : ofByte value.toByte = value := by
  cases value with
  | conditionalOrder => decide
  | firmUpOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ConditionalTypeValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ConditionalTypeValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ConditionalTypeValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ConditionalTypeValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ConditionalTypeValue

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  text : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (text, bytes) ← Alpha.decode 1 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : DebugPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DebugPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebugPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DebugPacket

/-- Login Request Packet: 46 bytes -/
structure LoginRequestPacket where
  username : Alpha 6
  password : Alpha 10
  requestedSession : Alpha 10
  requestedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginRequestPacket

def encode (message : LoginRequestPacket) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.requestedSession
    ++ (Alpha.encode message.requestedSequenceNumber)))

def decode (bytes : List UInt8) : Option (LoginRequestPacket × List UInt8) := do
  let (username, bytes) ← Alpha.decode 6 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (requestedSession, bytes) ← Alpha.decode 10 bytes
  let (requestedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ username, password, requestedSession, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequestPacket) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestPacket) (rest : List UInt8) :
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

end LoginRequestPacket

/-- Clearing Account: 12 bytes -/
structure ClearingAccount where
  clearingAccountValue : Alpha 12
  deriving DecidableEq, Repr

namespace ClearingAccount

def encode (message : ClearingAccount) : List UInt8 :=
  Alpha.encode message.clearingAccountValue

def decode (bytes : List UInt8) : Option (ClearingAccount × List UInt8) := do
  let (clearingAccountValue, bytes) ← Alpha.decode 12 bytes
  pure ({ clearingAccountValue }, bytes)

@[simp] theorem encode_length (message : ClearingAccount) : (encode message).length = 12 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ClearingAccount) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingAccount) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClearingAccount

/-- Clearing Account Type: 1 bytes -/
structure ClearingAccountType where
  clearingAccountTypeValue : ClearingAccountTypeValue
  deriving DecidableEq, Repr

namespace ClearingAccountType

def encode (message : ClearingAccountType) : List UInt8 :=
  ClearingAccountTypeValue.encode message.clearingAccountTypeValue

def decode (bytes : List UInt8) : Option (ClearingAccountType × List UInt8) := do
  let (clearingAccountTypeValue, bytes) ← ClearingAccountTypeValue.decode bytes
  pure ({ clearingAccountTypeValue }, bytes)

@[simp] theorem encode_length (message : ClearingAccountType) : (encode message).length = 1 := by
  unfold encode
  simp only [ClearingAccountTypeValue.encode_length]

theorem encode_length_pos (message : ClearingAccountType) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingAccountType) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ClearingAccountTypeValue.decode_encode, some_bind]
  rfl

end ClearingAccountType

/-- Clearing Firm: 4 bytes -/
structure ClearingFirm where
  clearingFirmValue : Alpha 4
  deriving DecidableEq, Repr

namespace ClearingFirm

def encode (message : ClearingFirm) : List UInt8 :=
  Alpha.encode message.clearingFirmValue

def decode (bytes : List UInt8) : Option (ClearingFirm × List UInt8) := do
  let (clearingFirmValue, bytes) ← Alpha.decode 4 bytes
  pure ({ clearingFirmValue }, bytes)

@[simp] theorem encode_length (message : ClearingFirm) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ClearingFirm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingFirm) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClearingFirm

/-- Client Reference: 15 bytes -/
structure ClientReference where
  clientReferenceValue : Alpha 15
  deriving DecidableEq, Repr

namespace ClientReference

def encode (message : ClientReference) : List UInt8 :=
  Alpha.encode message.clientReferenceValue

def decode (bytes : List UInt8) : Option (ClientReference × List UInt8) := do
  let (clientReferenceValue, bytes) ← Alpha.decode 15 bytes
  pure ({ clientReferenceValue }, bytes)

@[simp] theorem encode_length (message : ClientReference) : (encode message).length = 15 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ClientReference) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClientReference) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClientReference

/-- Cross Type: 1 bytes -/
structure CrossType where
  crossTypeValue : CrossTypeValue
  deriving DecidableEq, Repr

namespace CrossType

def encode (message : CrossType) : List UInt8 :=
  CrossTypeValue.encode message.crossTypeValue

def decode (bytes : List UInt8) : Option (CrossType × List UInt8) := do
  let (crossTypeValue, bytes) ← CrossTypeValue.decode bytes
  pure ({ crossTypeValue }, bytes)

@[simp] theorem encode_length (message : CrossType) : (encode message).length = 1 := by
  unfold encode
  simp only [CrossTypeValue.encode_length]

theorem encode_length_pos (message : CrossType) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossType) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [CrossTypeValue.decode_encode, some_bind]
  rfl

end CrossType

/-- Dea Indicator: 1 bytes -/
structure DeaIndicator where
  deaIndicatorValue : DeaIndicatorValue
  deriving DecidableEq, Repr

namespace DeaIndicator

def encode (message : DeaIndicator) : List UInt8 :=
  DeaIndicatorValue.encode message.deaIndicatorValue

def decode (bytes : List UInt8) : Option (DeaIndicator × List UInt8) := do
  let (deaIndicatorValue, bytes) ← DeaIndicatorValue.decode bytes
  pure ({ deaIndicatorValue }, bytes)

@[simp] theorem encode_length (message : DeaIndicator) : (encode message).length = 1 := by
  unfold encode
  simp only [DeaIndicatorValue.encode_length]

theorem encode_length_pos (message : DeaIndicator) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeaIndicator) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [DeaIndicatorValue.decode_encode, some_bind]
  rfl

end DeaIndicator

/-- Display: 1 bytes -/
structure Display where
  displayValue : DisplayValue
  deriving DecidableEq, Repr

namespace Display

def encode (message : Display) : List UInt8 :=
  DisplayValue.encode message.displayValue

def decode (bytes : List UInt8) : Option (Display × List UInt8) := do
  let (displayValue, bytes) ← DisplayValue.decode bytes
  pure ({ displayValue }, bytes)

@[simp] theorem encode_length (message : Display) : (encode message).length = 1 := by
  unfold encode
  simp only [DisplayValue.encode_length]

theorem encode_length_pos (message : Display) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Display) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [DisplayValue.decode_encode, some_bind]
  rfl

end Display

/-- Display Price: 4 bytes -/
structure DisplayPrice where
  displayPriceValue : BitVec 32
  deriving DecidableEq, Repr

namespace DisplayPrice

def encode (message : DisplayPrice) : List UInt8 :=
  encodeUInt 4 message.displayPriceValue

def decode (bytes : List UInt8) : Option (DisplayPrice × List UInt8) := do
  let (displayPriceValue, bytes) ← decodeUInt 4 bytes
  pure ({ displayPriceValue }, bytes)

@[simp] theorem encode_length (message : DisplayPrice) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : DisplayPrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisplayPrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DisplayPrice

/-- Display Quantity: 4 bytes -/
structure DisplayQuantity where
  displayQuantityValue : BitVec 32
  deriving DecidableEq, Repr

namespace DisplayQuantity

def encode (message : DisplayQuantity) : List UInt8 :=
  encodeUInt 4 message.displayQuantityValue

def decode (bytes : List UInt8) : Option (DisplayQuantity × List UInt8) := do
  let (displayQuantityValue, bytes) ← decodeUInt 4 bytes
  pure ({ displayQuantityValue }, bytes)

@[simp] theorem encode_length (message : DisplayQuantity) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : DisplayQuantity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisplayQuantity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DisplayQuantity

/-- Expire Time: 2 bytes -/
structure ExpireTime where
  expireTimeValue : BitVec 16
  deriving DecidableEq, Repr

namespace ExpireTime

def encode (message : ExpireTime) : List UInt8 :=
  encodeUInt 2 message.expireTimeValue

def decode (bytes : List UInt8) : Option (ExpireTime × List UInt8) := do
  let (expireTimeValue, bytes) ← decodeUInt 2 bytes
  pure ({ expireTimeValue }, bytes)

@[simp] theorem encode_length (message : ExpireTime) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ExpireTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExpireTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExpireTime

/-- Firm: 4 bytes -/
structure Firm where
  firmValue : Alpha 4
  deriving DecidableEq, Repr

namespace Firm

def encode (message : Firm) : List UInt8 :=
  Alpha.encode message.firmValue

def decode (bytes : List UInt8) : Option (Firm × List UInt8) := do
  let (firmValue, bytes) ← Alpha.decode 4 bytes
  pure ({ firmValue }, bytes)

@[simp] theorem encode_length (message : Firm) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : Firm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Firm) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end Firm

/-- Liquidity Provision Indicator: 1 bytes -/
structure LiquidityProvisionIndicator where
  liquidityProvisionIndicatorValue : LiquidityProvisionIndicatorValue
  deriving DecidableEq, Repr

namespace LiquidityProvisionIndicator

def encode (message : LiquidityProvisionIndicator) : List UInt8 :=
  LiquidityProvisionIndicatorValue.encode message.liquidityProvisionIndicatorValue

def decode (bytes : List UInt8) : Option (LiquidityProvisionIndicator × List UInt8) := do
  let (liquidityProvisionIndicatorValue, bytes) ← LiquidityProvisionIndicatorValue.decode bytes
  pure ({ liquidityProvisionIndicatorValue }, bytes)

@[simp] theorem encode_length (message : LiquidityProvisionIndicator) : (encode message).length = 1 := by
  unfold encode
  simp only [LiquidityProvisionIndicatorValue.encode_length]

theorem encode_length_pos (message : LiquidityProvisionIndicator) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LiquidityProvisionIndicator) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [LiquidityProvisionIndicatorValue.decode_encode, some_bind]
  rfl

end LiquidityProvisionIndicator

/-- Max Floor: 4 bytes -/
structure MaxFloor where
  maxFloorValue : BitVec 32
  deriving DecidableEq, Repr

namespace MaxFloor

def encode (message : MaxFloor) : List UInt8 :=
  encodeUInt 4 message.maxFloorValue

def decode (bytes : List UInt8) : Option (MaxFloor × List UInt8) := do
  let (maxFloorValue, bytes) ← decodeUInt 4 bytes
  pure ({ maxFloorValue }, bytes)

@[simp] theorem encode_length (message : MaxFloor) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MaxFloor) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaxFloor) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaxFloor

/-- Minimum Quantity: 4 bytes -/
structure MinimumQuantity where
  minimumQuantityValue : BitVec 32
  deriving DecidableEq, Repr

namespace MinimumQuantity

def encode (message : MinimumQuantity) : List UInt8 :=
  encodeUInt 4 message.minimumQuantityValue

def decode (bytes : List UInt8) : Option (MinimumQuantity × List UInt8) := do
  let (minimumQuantityValue, bytes) ← decodeUInt 4 bytes
  pure ({ minimumQuantityValue }, bytes)

@[simp] theorem encode_length (message : MinimumQuantity) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MinimumQuantity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinimumQuantity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinimumQuantity

/-- Order Reference: 10 bytes -/
structure OrderReference where
  orderReferenceValue : Alpha 10
  deriving DecidableEq, Repr

namespace OrderReference

def encode (message : OrderReference) : List UInt8 :=
  Alpha.encode message.orderReferenceValue

def decode (bytes : List UInt8) : Option (OrderReference × List UInt8) := do
  let (orderReferenceValue, bytes) ← Alpha.decode 10 bytes
  pure ({ orderReferenceValue }, bytes)

@[simp] theorem encode_length (message : OrderReference) : (encode message).length = 10 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : OrderReference) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReference) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderReference

/-- Original Order Entry Date: 4 bytes -/
structure OriginalOrderEntryDate where
  originalOrderEntryDateValue : BitVec 32
  deriving DecidableEq, Repr

namespace OriginalOrderEntryDate

def encode (message : OriginalOrderEntryDate) : List UInt8 :=
  encodeUInt 4 message.originalOrderEntryDateValue

def decode (bytes : List UInt8) : Option (OriginalOrderEntryDate × List UInt8) := do
  let (originalOrderEntryDateValue, bytes) ← decodeUInt 4 bytes
  pure ({ originalOrderEntryDateValue }, bytes)

@[simp] theorem encode_length (message : OriginalOrderEntryDate) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : OriginalOrderEntryDate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OriginalOrderEntryDate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OriginalOrderEntryDate

/-- Original Order Reference Number: 8 bytes -/
structure OriginalOrderReferenceNumber where
  originalOrderReferenceNumberValue : BitVec 64
  deriving DecidableEq, Repr

namespace OriginalOrderReferenceNumber

def encode (message : OriginalOrderReferenceNumber) : List UInt8 :=
  encodeUInt 8 message.originalOrderReferenceNumberValue

def decode (bytes : List UInt8) : Option (OriginalOrderReferenceNumber × List UInt8) := do
  let (originalOrderReferenceNumberValue, bytes) ← decodeUInt 8 bytes
  pure ({ originalOrderReferenceNumberValue }, bytes)

@[simp] theorem encode_length (message : OriginalOrderReferenceNumber) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : OriginalOrderReferenceNumber) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OriginalOrderReferenceNumber) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OriginalOrderReferenceNumber

/-- Peg Difference: 4 bytes -/
structure PegDifference where
  pegDifferenceValue : BitVec 32
  deriving DecidableEq, Repr

namespace PegDifference

def encode (message : PegDifference) : List UInt8 :=
  encodeUInt 4 message.pegDifferenceValue

def decode (bytes : List UInt8) : Option (PegDifference × List UInt8) := do
  let (pegDifferenceValue, bytes) ← decodeUInt 4 bytes
  pure ({ pegDifferenceValue }, bytes)

@[simp] theorem encode_length (message : PegDifference) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : PegDifference) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PegDifference) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PegDifference

/-- Peg Type: 1 bytes -/
structure PegType where
  pegTypeValue : PegTypeValue
  deriving DecidableEq, Repr

namespace PegType

def encode (message : PegType) : List UInt8 :=
  PegTypeValue.encode message.pegTypeValue

def decode (bytes : List UInt8) : Option (PegType × List UInt8) := do
  let (pegTypeValue, bytes) ← PegTypeValue.decode bytes
  pure ({ pegTypeValue }, bytes)

@[simp] theorem encode_length (message : PegType) : (encode message).length = 1 := by
  unfold encode
  simp only [PegTypeValue.encode_length]

theorem encode_length_pos (message : PegType) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PegType) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [PegTypeValue.decode_encode, some_bind]
  rfl

end PegType

/-- Random Reserve: 4 bytes -/
structure RandomReserve where
  randomReserveValue : BitVec 32
  deriving DecidableEq, Repr

namespace RandomReserve

def encode (message : RandomReserve) : List UInt8 :=
  encodeUInt 4 message.randomReserveValue

def decode (bytes : List UInt8) : Option (RandomReserve × List UInt8) := do
  let (randomReserveValue, bytes) ← decodeUInt 4 bytes
  pure ({ randomReserveValue }, bytes)

@[simp] theorem encode_length (message : RandomReserve) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : RandomReserve) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RandomReserve) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RandomReserve

/-- Secondary Order Reference Number: 8 bytes -/
structure SecondaryOrderReferenceNumber where
  secondaryOrderReferenceNumberValue : BitVec 64
  deriving DecidableEq, Repr

namespace SecondaryOrderReferenceNumber

def encode (message : SecondaryOrderReferenceNumber) : List UInt8 :=
  encodeUInt 8 message.secondaryOrderReferenceNumberValue

def decode (bytes : List UInt8) : Option (SecondaryOrderReferenceNumber × List UInt8) := do
  let (secondaryOrderReferenceNumberValue, bytes) ← decodeUInt 8 bytes
  pure ({ secondaryOrderReferenceNumberValue }, bytes)

@[simp] theorem encode_length (message : SecondaryOrderReferenceNumber) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecondaryOrderReferenceNumber) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondaryOrderReferenceNumber) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecondaryOrderReferenceNumber

/-- Stp Action: 1 bytes -/
structure StpAction where
  stpActionValue : StpActionValue
  deriving DecidableEq, Repr

namespace StpAction

def encode (message : StpAction) : List UInt8 :=
  StpActionValue.encode message.stpActionValue

def decode (bytes : List UInt8) : Option (StpAction × List UInt8) := do
  let (stpActionValue, bytes) ← StpActionValue.decode bytes
  pure ({ stpActionValue }, bytes)

@[simp] theorem encode_length (message : StpAction) : (encode message).length = 1 := by
  unfold encode
  simp only [StpActionValue.encode_length]

theorem encode_length_pos (message : StpAction) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StpAction) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [StpActionValue.decode_encode, some_bind]
  rfl

end StpAction

/-- Stp Level: 1 bytes -/
structure StpLevel where
  stpLevelValue : StpLevelValue
  deriving DecidableEq, Repr

namespace StpLevel

def encode (message : StpLevel) : List UInt8 :=
  StpLevelValue.encode message.stpLevelValue

def decode (bytes : List UInt8) : Option (StpLevel × List UInt8) := do
  let (stpLevelValue, bytes) ← StpLevelValue.decode bytes
  pure ({ stpLevelValue }, bytes)

@[simp] theorem encode_length (message : StpLevel) : (encode message).length = 1 := by
  unfold encode
  simp only [StpLevelValue.encode_length]

theorem encode_length_pos (message : StpLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StpLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [StpLevelValue.decode_encode, some_bind]
  rfl

end StpLevel

/-- Stp Trader Group: 2 bytes -/
structure StpTraderGroup where
  stpTraderGroupValue : Alpha 2
  deriving DecidableEq, Repr

namespace StpTraderGroup

def encode (message : StpTraderGroup) : List UInt8 :=
  Alpha.encode message.stpTraderGroupValue

def decode (bytes : List UInt8) : Option (StpTraderGroup × List UInt8) := do
  let (stpTraderGroupValue, bytes) ← Alpha.decode 2 bytes
  pure ({ stpTraderGroupValue }, bytes)

@[simp] theorem encode_length (message : StpTraderGroup) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : StpTraderGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StpTraderGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end StpTraderGroup

/-- Time In Force: 1 bytes -/
structure TimeInForce where
  timeInForceValue : TimeInForceValue
  deriving DecidableEq, Repr

namespace TimeInForce

def encode (message : TimeInForce) : List UInt8 :=
  TimeInForceValue.encode message.timeInForceValue

def decode (bytes : List UInt8) : Option (TimeInForce × List UInt8) := do
  let (timeInForceValue, bytes) ← TimeInForceValue.decode bytes
  pure ({ timeInForceValue }, bytes)

@[simp] theorem encode_length (message : TimeInForce) : (encode message).length = 1 := by
  unfold encode
  simp only [TimeInForceValue.encode_length]

theorem encode_length_pos (message : TimeInForce) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeInForce) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [TimeInForceValue.decode_encode, some_bind]
  rfl

end TimeInForce

/-- Trading At Closing Price: 1 bytes -/
structure TradingAtClosingPrice where
  tradingAtClosingPriceValue : TradingAtClosingPriceValue
  deriving DecidableEq, Repr

namespace TradingAtClosingPrice

def encode (message : TradingAtClosingPrice) : List UInt8 :=
  TradingAtClosingPriceValue.encode message.tradingAtClosingPriceValue

def decode (bytes : List UInt8) : Option (TradingAtClosingPrice × List UInt8) := do
  let (tradingAtClosingPriceValue, bytes) ← TradingAtClosingPriceValue.decode bytes
  pure ({ tradingAtClosingPriceValue }, bytes)

@[simp] theorem encode_length (message : TradingAtClosingPrice) : (encode message).length = 1 := by
  unfold encode
  simp only [TradingAtClosingPriceValue.encode_length]

theorem encode_length_pos (message : TradingAtClosingPrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingAtClosingPrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [TradingAtClosingPriceValue.decode_encode, some_bind]
  rfl

end TradingAtClosingPrice

/-- Order Condition: 1 bytes -/
structure OrderCondition where
  orderConditionValue : OrderConditionValue
  deriving DecidableEq, Repr

namespace OrderCondition

def encode (message : OrderCondition) : List UInt8 :=
  OrderConditionValue.encode message.orderConditionValue

def decode (bytes : List UInt8) : Option (OrderCondition × List UInt8) := do
  let (orderConditionValue, bytes) ← OrderConditionValue.decode bytes
  pure ({ orderConditionValue }, bytes)

@[simp] theorem encode_length (message : OrderCondition) : (encode message).length = 1 := by
  unfold encode
  simp only [OrderConditionValue.encode_length]

theorem encode_length_pos (message : OrderCondition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCondition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [OrderConditionValue.decode_encode, some_bind]
  rfl

end OrderCondition

/-- Cumulative Quantity: 4 bytes -/
structure CumulativeQuantity where
  cumulativeQuantityValue : BitVec 32
  deriving DecidableEq, Repr

namespace CumulativeQuantity

def encode (message : CumulativeQuantity) : List UInt8 :=
  encodeUInt 4 message.cumulativeQuantityValue

def decode (bytes : List UInt8) : Option (CumulativeQuantity × List UInt8) := do
  let (cumulativeQuantityValue, bytes) ← decodeUInt 4 bytes
  pure ({ cumulativeQuantityValue }, bytes)

@[simp] theorem encode_length (message : CumulativeQuantity) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : CumulativeQuantity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CumulativeQuantity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CumulativeQuantity

/-- Customer Order Capacity: 1 bytes -/
structure CustomerOrderCapacity where
  customerOrderCapacityValue : CustomerOrderCapacityValue
  deriving DecidableEq, Repr

namespace CustomerOrderCapacity

def encode (message : CustomerOrderCapacity) : List UInt8 :=
  CustomerOrderCapacityValue.encode message.customerOrderCapacityValue

def decode (bytes : List UInt8) : Option (CustomerOrderCapacity × List UInt8) := do
  let (customerOrderCapacityValue, bytes) ← CustomerOrderCapacityValue.decode bytes
  pure ({ customerOrderCapacityValue }, bytes)

@[simp] theorem encode_length (message : CustomerOrderCapacity) : (encode message).length = 1 := by
  unfold encode
  simp only [CustomerOrderCapacityValue.encode_length]

theorem encode_length_pos (message : CustomerOrderCapacity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CustomerOrderCapacity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [CustomerOrderCapacityValue.decode_encode, some_bind]
  rfl

end CustomerOrderCapacity

/-- Target Strategy: 1 bytes -/
structure TargetStrategy where
  targetStrategyValue : TargetStrategyValue
  deriving DecidableEq, Repr

namespace TargetStrategy

def encode (message : TargetStrategy) : List UInt8 :=
  TargetStrategyValue.encode message.targetStrategyValue

def decode (bytes : List UInt8) : Option (TargetStrategy × List UInt8) := do
  let (targetStrategyValue, bytes) ← TargetStrategyValue.decode bytes
  pure ({ targetStrategyValue }, bytes)

@[simp] theorem encode_length (message : TargetStrategy) : (encode message).length = 1 := by
  unfold encode
  simp only [TargetStrategyValue.encode_length]

theorem encode_length_pos (message : TargetStrategy) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TargetStrategy) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [TargetStrategyValue.decode_encode, some_bind]
  rfl

end TargetStrategy

/-- Min Rate: 2 bytes -/
structure MinRate where
  minRateValue : BitVec 16
  deriving DecidableEq, Repr

namespace MinRate

def encode (message : MinRate) : List UInt8 :=
  encodeUInt 2 message.minRateValue

def decode (bytes : List UInt8) : Option (MinRate × List UInt8) := do
  let (minRateValue, bytes) ← decodeUInt 2 bytes
  pure ({ minRateValue }, bytes)

@[simp] theorem encode_length (message : MinRate) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MinRate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinRate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinRate

/-- Max Rate: 2 bytes -/
structure MaxRate where
  maxRateValue : BitVec 16
  deriving DecidableEq, Repr

namespace MaxRate

def encode (message : MaxRate) : List UInt8 :=
  encodeUInt 2 message.maxRateValue

def decode (bytes : List UInt8) : Option (MaxRate × List UInt8) := do
  let (maxRateValue, bytes) ← decodeUInt 2 bytes
  pure ({ maxRateValue }, bytes)

@[simp] theorem encode_length (message : MaxRate) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MaxRate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaxRate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaxRate

/-- Conditional Type: 1 bytes -/
structure ConditionalType where
  conditionalTypeValue : ConditionalTypeValue
  deriving DecidableEq, Repr

namespace ConditionalType

def encode (message : ConditionalType) : List UInt8 :=
  ConditionalTypeValue.encode message.conditionalTypeValue

def decode (bytes : List UInt8) : Option (ConditionalType × List UInt8) := do
  let (conditionalTypeValue, bytes) ← ConditionalTypeValue.decode bytes
  pure ({ conditionalTypeValue }, bytes)

@[simp] theorem encode_length (message : ConditionalType) : (encode message).length = 1 := by
  unfold encode
  simp only [ConditionalTypeValue.encode_length]

theorem encode_length_pos (message : ConditionalType) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConditionalType) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ConditionalTypeValue.decode_encode, some_bind]
  rfl

end ConditionalType

/-- Firm Up Id: 4 bytes -/
structure FirmUpId where
  firmUpIdValue : BitVec 32
  deriving DecidableEq, Repr

namespace FirmUpId

def encode (message : FirmUpId) : List UInt8 :=
  encodeUInt 4 message.firmUpIdValue

def decode (bytes : List UInt8) : Option (FirmUpId × List UInt8) := do
  let (firmUpIdValue, bytes) ← decodeUInt 4 bytes
  pure ({ firmUpIdValue }, bytes)

@[simp] theorem encode_length (message : FirmUpId) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : FirmUpId) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FirmUpId) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FirmUpId

/-- Any Value Payload, selected by Tag -/
inductive ValuePayload where
  | clearingAccount (message : ClearingAccount) -- 1
  | clearingAccountType (message : ClearingAccountType) -- 2
  | clearingFirm (message : ClearingFirm) -- 3
  | clientReference (message : ClientReference) -- 4
  | crossType (message : CrossType) -- 5
  | deaIndicator (message : DeaIndicator) -- 6
  | display (message : Display) -- 7
  | displayPrice (message : DisplayPrice) -- 8
  | displayQuantity (message : DisplayQuantity) -- 9
  | expireTime (message : ExpireTime) -- 10
  | firm (message : Firm) -- 11
  | liquidityProvisionIndicator (message : LiquidityProvisionIndicator) -- 12
  | maxFloor (message : MaxFloor) -- 13
  | minimumQuantity (message : MinimumQuantity) -- 14
  | orderReference (message : OrderReference) -- 15
  | originalOrderEntryDate (message : OriginalOrderEntryDate) -- 16
  | originalOrderReferenceNumber (message : OriginalOrderReferenceNumber) -- 17
  | pegDifference (message : PegDifference) -- 18
  | pegType (message : PegType) -- 19
  | randomReserve (message : RandomReserve) -- 20
  | secondaryOrderReferenceNumber (message : SecondaryOrderReferenceNumber) -- 21
  | stpAction (message : StpAction) -- 22
  | stpLevel (message : StpLevel) -- 23
  | stpTraderGroup (message : StpTraderGroup) -- 24
  | timeInForce (message : TimeInForce) -- 25
  | tradingAtClosingPrice (message : TradingAtClosingPrice) -- 26
  | orderCondition (message : OrderCondition) -- 27
  | cumulativeQuantity (message : CumulativeQuantity) -- 28
  | customerOrderCapacity (message : CustomerOrderCapacity) -- 29
  | targetStrategy (message : TargetStrategy) -- 30
  | minRate (message : MinRate) -- 31
  | maxRate (message : MaxRate) -- 32
  | conditionalType (message : ConditionalType) -- 33
  | firmUpId (message : FirmUpId) -- 34
  deriving DecidableEq, Repr

namespace ValuePayload

/-- The Tag each message is sent under -/
def tag : ValuePayload → BitVec 8
  | .clearingAccount _ => 1
  | .clearingAccountType _ => 2
  | .clearingFirm _ => 3
  | .clientReference _ => 4
  | .crossType _ => 5
  | .deaIndicator _ => 6
  | .display _ => 7
  | .displayPrice _ => 8
  | .displayQuantity _ => 9
  | .expireTime _ => 10
  | .firm _ => 11
  | .liquidityProvisionIndicator _ => 12
  | .maxFloor _ => 13
  | .minimumQuantity _ => 14
  | .orderReference _ => 15
  | .originalOrderEntryDate _ => 16
  | .originalOrderReferenceNumber _ => 17
  | .pegDifference _ => 18
  | .pegType _ => 19
  | .randomReserve _ => 20
  | .secondaryOrderReferenceNumber _ => 21
  | .stpAction _ => 22
  | .stpLevel _ => 23
  | .stpTraderGroup _ => 24
  | .timeInForce _ => 25
  | .tradingAtClosingPrice _ => 26
  | .orderCondition _ => 27
  | .cumulativeQuantity _ => 28
  | .customerOrderCapacity _ => 29
  | .targetStrategy _ => 30
  | .minRate _ => 31
  | .maxRate _ => 32
  | .conditionalType _ => 33
  | .firmUpId _ => 34

def encode : ValuePayload → List UInt8
  | .clearingAccount message => ClearingAccount.encode message
  | .clearingAccountType message => ClearingAccountType.encode message
  | .clearingFirm message => ClearingFirm.encode message
  | .clientReference message => ClientReference.encode message
  | .crossType message => CrossType.encode message
  | .deaIndicator message => DeaIndicator.encode message
  | .display message => Display.encode message
  | .displayPrice message => DisplayPrice.encode message
  | .displayQuantity message => DisplayQuantity.encode message
  | .expireTime message => ExpireTime.encode message
  | .firm message => Firm.encode message
  | .liquidityProvisionIndicator message => LiquidityProvisionIndicator.encode message
  | .maxFloor message => MaxFloor.encode message
  | .minimumQuantity message => MinimumQuantity.encode message
  | .orderReference message => OrderReference.encode message
  | .originalOrderEntryDate message => OriginalOrderEntryDate.encode message
  | .originalOrderReferenceNumber message => OriginalOrderReferenceNumber.encode message
  | .pegDifference message => PegDifference.encode message
  | .pegType message => PegType.encode message
  | .randomReserve message => RandomReserve.encode message
  | .secondaryOrderReferenceNumber message => SecondaryOrderReferenceNumber.encode message
  | .stpAction message => StpAction.encode message
  | .stpLevel message => StpLevel.encode message
  | .stpTraderGroup message => StpTraderGroup.encode message
  | .timeInForce message => TimeInForce.encode message
  | .tradingAtClosingPrice message => TradingAtClosingPrice.encode message
  | .orderCondition message => OrderCondition.encode message
  | .cumulativeQuantity message => CumulativeQuantity.encode message
  | .customerOrderCapacity message => CustomerOrderCapacity.encode message
  | .targetStrategy message => TargetStrategy.encode message
  | .minRate message => MinRate.encode message
  | .maxRate message => MaxRate.encode message
  | .conditionalType message => ConditionalType.encode message
  | .firmUpId message => FirmUpId.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ValuePayload) : (encode message).length ≤ 15 := by
  cases message with
  | clearingAccount inner =>
    simp only [encode, ClearingAccount.encode_length]
    omega
  | clearingAccountType inner =>
    simp only [encode, ClearingAccountType.encode_length]
    omega
  | clearingFirm inner =>
    simp only [encode, ClearingFirm.encode_length]
    omega
  | clientReference inner =>
    simp only [encode, ClientReference.encode_length]
    omega
  | crossType inner =>
    simp only [encode, CrossType.encode_length]
    omega
  | deaIndicator inner =>
    simp only [encode, DeaIndicator.encode_length]
    omega
  | display inner =>
    simp only [encode, Display.encode_length]
    omega
  | displayPrice inner =>
    simp only [encode, DisplayPrice.encode_length]
    omega
  | displayQuantity inner =>
    simp only [encode, DisplayQuantity.encode_length]
    omega
  | expireTime inner =>
    simp only [encode, ExpireTime.encode_length]
    omega
  | firm inner =>
    simp only [encode, Firm.encode_length]
    omega
  | liquidityProvisionIndicator inner =>
    simp only [encode, LiquidityProvisionIndicator.encode_length]
    omega
  | maxFloor inner =>
    simp only [encode, MaxFloor.encode_length]
    omega
  | minimumQuantity inner =>
    simp only [encode, MinimumQuantity.encode_length]
    omega
  | orderReference inner =>
    simp only [encode, OrderReference.encode_length]
    omega
  | originalOrderEntryDate inner =>
    simp only [encode, OriginalOrderEntryDate.encode_length]
    omega
  | originalOrderReferenceNumber inner =>
    simp only [encode, OriginalOrderReferenceNumber.encode_length]
    omega
  | pegDifference inner =>
    simp only [encode, PegDifference.encode_length]
    omega
  | pegType inner =>
    simp only [encode, PegType.encode_length]
    omega
  | randomReserve inner =>
    simp only [encode, RandomReserve.encode_length]
    omega
  | secondaryOrderReferenceNumber inner =>
    simp only [encode, SecondaryOrderReferenceNumber.encode_length]
    omega
  | stpAction inner =>
    simp only [encode, StpAction.encode_length]
    omega
  | stpLevel inner =>
    simp only [encode, StpLevel.encode_length]
    omega
  | stpTraderGroup inner =>
    simp only [encode, StpTraderGroup.encode_length]
    omega
  | timeInForce inner =>
    simp only [encode, TimeInForce.encode_length]
    omega
  | tradingAtClosingPrice inner =>
    simp only [encode, TradingAtClosingPrice.encode_length]
    omega
  | orderCondition inner =>
    simp only [encode, OrderCondition.encode_length]
    omega
  | cumulativeQuantity inner =>
    simp only [encode, CumulativeQuantity.encode_length]
    omega
  | customerOrderCapacity inner =>
    simp only [encode, CustomerOrderCapacity.encode_length]
    omega
  | targetStrategy inner =>
    simp only [encode, TargetStrategy.encode_length]
    omega
  | minRate inner =>
    simp only [encode, MinRate.encode_length]
    omega
  | maxRate inner =>
    simp only [encode, MaxRate.encode_length]
    omega
  | conditionalType inner =>
    simp only [encode, ConditionalType.encode_length]
    omega
  | firmUpId inner =>
    simp only [encode, FirmUpId.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ValuePayload × List UInt8) :=
  if tag = 1 then (ClearingAccount.decode bytes).map fun (message, rest) => (.clearingAccount message, rest)
  else if tag = 2 then (ClearingAccountType.decode bytes).map fun (message, rest) => (.clearingAccountType message, rest)
  else if tag = 3 then (ClearingFirm.decode bytes).map fun (message, rest) => (.clearingFirm message, rest)
  else if tag = 4 then (ClientReference.decode bytes).map fun (message, rest) => (.clientReference message, rest)
  else if tag = 5 then (CrossType.decode bytes).map fun (message, rest) => (.crossType message, rest)
  else if tag = 6 then (DeaIndicator.decode bytes).map fun (message, rest) => (.deaIndicator message, rest)
  else if tag = 7 then (Display.decode bytes).map fun (message, rest) => (.display message, rest)
  else if tag = 8 then (DisplayPrice.decode bytes).map fun (message, rest) => (.displayPrice message, rest)
  else if tag = 9 then (DisplayQuantity.decode bytes).map fun (message, rest) => (.displayQuantity message, rest)
  else if tag = 10 then (ExpireTime.decode bytes).map fun (message, rest) => (.expireTime message, rest)
  else if tag = 11 then (Firm.decode bytes).map fun (message, rest) => (.firm message, rest)
  else if tag = 12 then (LiquidityProvisionIndicator.decode bytes).map fun (message, rest) => (.liquidityProvisionIndicator message, rest)
  else if tag = 13 then (MaxFloor.decode bytes).map fun (message, rest) => (.maxFloor message, rest)
  else if tag = 14 then (MinimumQuantity.decode bytes).map fun (message, rest) => (.minimumQuantity message, rest)
  else if tag = 15 then (OrderReference.decode bytes).map fun (message, rest) => (.orderReference message, rest)
  else if tag = 16 then (OriginalOrderEntryDate.decode bytes).map fun (message, rest) => (.originalOrderEntryDate message, rest)
  else if tag = 17 then (OriginalOrderReferenceNumber.decode bytes).map fun (message, rest) => (.originalOrderReferenceNumber message, rest)
  else if tag = 18 then (PegDifference.decode bytes).map fun (message, rest) => (.pegDifference message, rest)
  else if tag = 19 then (PegType.decode bytes).map fun (message, rest) => (.pegType message, rest)
  else if tag = 20 then (RandomReserve.decode bytes).map fun (message, rest) => (.randomReserve message, rest)
  else if tag = 21 then (SecondaryOrderReferenceNumber.decode bytes).map fun (message, rest) => (.secondaryOrderReferenceNumber message, rest)
  else if tag = 22 then (StpAction.decode bytes).map fun (message, rest) => (.stpAction message, rest)
  else if tag = 23 then (StpLevel.decode bytes).map fun (message, rest) => (.stpLevel message, rest)
  else if tag = 24 then (StpTraderGroup.decode bytes).map fun (message, rest) => (.stpTraderGroup message, rest)
  else if tag = 25 then (TimeInForce.decode bytes).map fun (message, rest) => (.timeInForce message, rest)
  else if tag = 26 then (TradingAtClosingPrice.decode bytes).map fun (message, rest) => (.tradingAtClosingPrice message, rest)
  else if tag = 27 then (OrderCondition.decode bytes).map fun (message, rest) => (.orderCondition message, rest)
  else if tag = 28 then (CumulativeQuantity.decode bytes).map fun (message, rest) => (.cumulativeQuantity message, rest)
  else if tag = 29 then (CustomerOrderCapacity.decode bytes).map fun (message, rest) => (.customerOrderCapacity message, rest)
  else if tag = 30 then (TargetStrategy.decode bytes).map fun (message, rest) => (.targetStrategy message, rest)
  else if tag = 31 then (MinRate.decode bytes).map fun (message, rest) => (.minRate message, rest)
  else if tag = 32 then (MaxRate.decode bytes).map fun (message, rest) => (.maxRate message, rest)
  else if tag = 33 then (ConditionalType.decode bytes).map fun (message, rest) => (.conditionalType message, rest)
  else if tag = 34 then (FirmUpId.decode bytes).map fun (message, rest) => (.firmUpId message, rest)
  else none

@[simp] theorem decode_encode (message : ValuePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ValuePayload

/-- TagValue -/
structure Tagvalue where
  valuePayload : ValuePayload
  deriving DecidableEq, Repr

namespace Tagvalue

def encodeBody (message : Tagvalue) : List UInt8 :=
  encodeUInt 1 (ValuePayload.tag message.valuePayload)
    ++ (ValuePayload.encode message.valuePayload)

def decodeBody (bytes : List UInt8) : Option (Tagvalue × List UInt8) := do
  let (tag, bytes) ← decodeUInt 1 bytes
  let (valuePayload, bytes) ← ValuePayload.decode tag bytes
  pure ({ valuePayload }, bytes)

theorem decodeBody_encodeBody (message : Tagvalue) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ValuePayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Tagvalue) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.valuePayload with
  | clearingAccount inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, ClearingAccount.encode_length]
    omega
  | clearingAccountType inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, ClearingAccountType.encode_length]
    omega
  | clearingFirm inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, ClearingFirm.encode_length]
    omega
  | clientReference inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, ClientReference.encode_length]
    omega
  | crossType inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, CrossType.encode_length]
    omega
  | deaIndicator inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, DeaIndicator.encode_length]
    omega
  | display inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, Display.encode_length]
    omega
  | displayPrice inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, DisplayPrice.encode_length]
    omega
  | displayQuantity inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, DisplayQuantity.encode_length]
    omega
  | expireTime inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, ExpireTime.encode_length]
    omega
  | firm inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, Firm.encode_length]
    omega
  | liquidityProvisionIndicator inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, LiquidityProvisionIndicator.encode_length]
    omega
  | maxFloor inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, MaxFloor.encode_length]
    omega
  | minimumQuantity inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, MinimumQuantity.encode_length]
    omega
  | orderReference inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, OrderReference.encode_length]
    omega
  | originalOrderEntryDate inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, OriginalOrderEntryDate.encode_length]
    omega
  | originalOrderReferenceNumber inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, OriginalOrderReferenceNumber.encode_length]
    omega
  | pegDifference inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, PegDifference.encode_length]
    omega
  | pegType inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, PegType.encode_length]
    omega
  | randomReserve inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, RandomReserve.encode_length]
    omega
  | secondaryOrderReferenceNumber inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, SecondaryOrderReferenceNumber.encode_length]
    omega
  | stpAction inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, StpAction.encode_length]
    omega
  | stpLevel inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, StpLevel.encode_length]
    omega
  | stpTraderGroup inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, StpTraderGroup.encode_length]
    omega
  | timeInForce inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, TimeInForce.encode_length]
    omega
  | tradingAtClosingPrice inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, TradingAtClosingPrice.encode_length]
    omega
  | orderCondition inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, OrderCondition.encode_length]
    omega
  | cumulativeQuantity inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, CumulativeQuantity.encode_length]
    omega
  | customerOrderCapacity inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, CustomerOrderCapacity.encode_length]
    omega
  | targetStrategy inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, TargetStrategy.encode_length]
    omega
  | minRate inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, MinRate.encode_length]
    omega
  | maxRate inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, MaxRate.encode_length]
    omega
  | conditionalType inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, ConditionalType.encode_length]
    omega
  | firmUpId inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, FirmUpId.encode_length]
    omega

/-- Size rule: Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Tagvalue → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (Tagvalue × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : Tagvalue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Tagvalue) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Tagvalue

/-- Enter Order Message -/
structure EnterOrderMessage where
  userRefNum : BitVec 32
  buySellIndicator : BuySellIndicator
  quantity : BitVec 32
  orderBook : BitVec 32
  price : BitVec 32
  user : Alpha 6
  executionWithinFirm : BitVec 32
  investmentDecisionWithinFirmShortCode : BitVec 32
  clientIdentifier : BitVec 32
  partyRoleQualifier : BitVec 8
  capacity : Capacity
  algoIndicator : AlgoIndicator
  tagvalue : Sized 2 Tagvalue.encode
  deriving DecidableEq, Repr

namespace EnterOrderMessage

def encode (message : EnterOrderMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.orderBook
    ++ (encodeUInt 4 message.price
    ++ (Alpha.encode message.user
    ++ (encodeUInt 4 message.executionWithinFirm
    ++ (encodeUInt 4 message.investmentDecisionWithinFirmShortCode
    ++ (encodeUInt 4 message.clientIdentifier
    ++ (encodeUInt 1 message.partyRoleQualifier
    ++ (Capacity.encode message.capacity
    ++ (AlgoIndicator.encode message.algoIndicator
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany Tagvalue.encode message.tagvalue.val).length)
    ++ (encodeMany Tagvalue.encode message.tagvalue.val)))))))))))))

def decode (bytes : List UInt8) : Option (EnterOrderMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (user, bytes) ← Alpha.decode 6 bytes
  let (executionWithinFirm, bytes) ← decodeUInt 4 bytes
  let (investmentDecisionWithinFirmShortCode, bytes) ← decodeUInt 4 bytes
  let (clientIdentifier, bytes) ← decodeUInt 4 bytes
  let (partyRoleQualifier, bytes) ← decodeUInt 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (algoIndicator, bytes) ← AlgoIndicator.decode bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (tagvalue_, bytes) ← decodeSized Tagvalue.decode appendageLength.toNat bytes
  if fits_tagvalue : (encodeMany Tagvalue.encode tagvalue_).length < 256 ^ 2 then
    pure ({ userRefNum, buySellIndicator, quantity, orderBook, price, user, executionWithinFirm, investmentDecisionWithinFirmShortCode, clientIdentifier, partyRoleQualifier, capacity, algoIndicator, tagvalue := ⟨tagvalue_, fits_tagvalue⟩ }, bytes)
  else none

theorem encode_length_pos (message : EnterOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EnterOrderMessage) : (encode message).length ≤ 65575 := by
  have bound_tagvalue := message.tagvalue.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, BuySellIndicator.encode_length, Alpha.encode_length, Capacity.encode_length, AlgoIndicator.encode_length]
  omega

@[simp] theorem decode_encode (message : EnterOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AlgoIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 Tagvalue.encode Tagvalue.decode Tagvalue.decode_encode Tagvalue.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.tagvalue.length_lt]
  rfl

end EnterOrderMessage

/-- Replace Order Message -/
structure ReplaceOrderMessage where
  origUserRefNum : BitVec 32
  newUserRefNum : BitVec 32
  quantity : BitVec 32
  price : BitVec 32
  user : Alpha 6
  tagvalue : Sized 2 Tagvalue.encode
  deriving DecidableEq, Repr

namespace ReplaceOrderMessage

def encode (message : ReplaceOrderMessage) : List UInt8 :=
  encodeUInt 4 message.origUserRefNum
    ++ (encodeUInt 4 message.newUserRefNum
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.price
    ++ (Alpha.encode message.user
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany Tagvalue.encode message.tagvalue.val).length)
    ++ (encodeMany Tagvalue.encode message.tagvalue.val))))))

def decode (bytes : List UInt8) : Option (ReplaceOrderMessage × List UInt8) := do
  let (origUserRefNum, bytes) ← decodeUInt 4 bytes
  let (newUserRefNum, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (user, bytes) ← Alpha.decode 6 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (tagvalue_, bytes) ← decodeSized Tagvalue.decode appendageLength.toNat bytes
  if fits_tagvalue : (encodeMany Tagvalue.encode tagvalue_).length < 256 ^ 2 then
    pure ({ origUserRefNum, newUserRefNum, quantity, price, user, tagvalue := ⟨tagvalue_, fits_tagvalue⟩ }, bytes)
  else none

theorem encode_length_pos (message : ReplaceOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReplaceOrderMessage) : (encode message).length ≤ 65559 := by
  have bound_tagvalue := message.tagvalue.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : ReplaceOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 Tagvalue.encode Tagvalue.decode Tagvalue.decode_encode Tagvalue.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.tagvalue.length_lt]
  rfl

end ReplaceOrderMessage

/-- Cancel Order Message: 14 bytes -/
structure CancelOrderMessage where
  userRefNum : BitVec 32
  quantity : BitVec 32
  user : Alpha 6
  deriving DecidableEq, Repr

namespace CancelOrderMessage

def encode (message : CancelOrderMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.quantity
    ++ (Alpha.encode message.user))

def decode (bytes : List UInt8) : Option (CancelOrderMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (user, bytes) ← Alpha.decode 6 bytes
  pure ({ userRefNum, quantity, user }, bytes)

@[simp] theorem encode_length (message : CancelOrderMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : CancelOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelOrderMessage

/-- Account Query Message: 0 bytes -/
structure AccountQueryMessage where
  deriving DecidableEq, Repr

namespace AccountQueryMessage

def encode (_ : AccountQueryMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (AccountQueryMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : AccountQueryMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : AccountQueryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end AccountQueryMessage

/-- Mmi Notification Request Message: 20 bytes -/
structure MmiNotificationRequestMessage where
  userRefNum : BitVec 32
  orderBook : BitVec 32
  instruction : Alpha 1
  addOrRemove : Alpha 1
  firm : Firm
  user : Alpha 6
  deriving DecidableEq, Repr

namespace MmiNotificationRequestMessage

def encode (message : MmiNotificationRequestMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.orderBook
    ++ (Alpha.encode message.instruction
    ++ (Alpha.encode message.addOrRemove
    ++ (Firm.encode message.firm
    ++ (Alpha.encode message.user)))))

def decode (bytes : List UInt8) : Option (MmiNotificationRequestMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (instruction, bytes) ← Alpha.decode 1 bytes
  let (addOrRemove, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Firm.decode bytes
  let (user, bytes) ← Alpha.decode 6 bytes
  pure ({ userRefNum, orderBook, instruction, addOrRemove, firm, user }, bytes)

@[simp] theorem encode_length (message : MmiNotificationRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Firm.encode_length]

theorem encode_length_pos (message : MmiNotificationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmiNotificationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Firm.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MmiNotificationRequestMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | enterOrderMessage (message : EnterOrderMessage) -- 'O' 0x4F
  | replaceOrderMessage (message : ReplaceOrderMessage) -- 'U' 0x55
  | cancelOrderMessage (message : CancelOrderMessage) -- 'X' 0x58
  | accountQueryMessage (message : AccountQueryMessage) -- 'Q' 0x51
  | mmiNotificationRequestMessage (message : MmiNotificationRequestMessage) -- 'M' 0x4D
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .enterOrderMessage _ => 79
  | .replaceOrderMessage _ => 85
  | .cancelOrderMessage _ => 88
  | .accountQueryMessage _ => 81
  | .mmiNotificationRequestMessage _ => 77

def encode : UnsequencedMessage → List UInt8
  | .enterOrderMessage message => EnterOrderMessage.encode message
  | .replaceOrderMessage message => ReplaceOrderMessage.encode message
  | .cancelOrderMessage message => CancelOrderMessage.encode message
  | .accountQueryMessage message => AccountQueryMessage.encode message
  | .mmiNotificationRequestMessage message => MmiNotificationRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 65575 := by
  cases message with
  | enterOrderMessage inner =>
    have bound_inner := EnterOrderMessage.encode_length_le inner
    simp only [encode]
    omega
  | replaceOrderMessage inner =>
    have bound_inner := ReplaceOrderMessage.encode_length_le inner
    simp only [encode]
    omega
  | cancelOrderMessage inner =>
    simp only [encode, CancelOrderMessage.encode_length]
    omega
  | accountQueryMessage inner =>
    simp only [encode, AccountQueryMessage.encode_length]
    omega
  | mmiNotificationRequestMessage inner =>
    simp only [encode, MmiNotificationRequestMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 79 then (EnterOrderMessage.decode bytes).map fun (message, rest) => (.enterOrderMessage message, rest)
  else if tag = 85 then (ReplaceOrderMessage.decode bytes).map fun (message, rest) => (.replaceOrderMessage message, rest)
  else if tag = 88 then (CancelOrderMessage.decode bytes).map fun (message, rest) => (.cancelOrderMessage message, rest)
  else if tag = 81 then (AccountQueryMessage.decode bytes).map fun (message, rest) => (.accountQueryMessage message, rest)
  else if tag = 77 then (MmiNotificationRequestMessage.decode bytes).map fun (message, rest) => (.mmiNotificationRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 65576 := by
  unfold encode
  cases message.unsequencedMessage with
  | enterOrderMessage inner =>
    have bound_inner := EnterOrderMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | replaceOrderMessage inner =>
    have bound_inner := ReplaceOrderMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | cancelOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderMessage.encode_length]
    omega
  | accountQueryMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, AccountQueryMessage.encode_length]
    omega
  | mmiNotificationRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MmiNotificationRequestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

end UnsequencedDataPacket

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ClientHeartbeat

/-- Logout Request: 0 bytes -/
structure LogoutRequest where
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (_ : LogoutRequest) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequest × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequest) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutRequest

/-- Any Client Payload, selected by Client Packet Type -/
inductive ClientPayload where
  | debugPacket (message : DebugPacket) -- '+' 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- 'L' 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- 'U' 0x55
  | clientHeartbeat (message : ClientHeartbeat) -- 'R' 0x52
  | logoutRequest (message : LogoutRequest) -- 'O' 0x4F
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .unsequencedDataPacket _ => 85
  | .clientHeartbeat _ => 82
  | .logoutRequest _ => 79

def encode : ClientPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message
  | .logoutRequest message => LogoutRequest.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 65576 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [encode, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | clientHeartbeat inner =>
    simp only [encode, ClientHeartbeat.encode_length]
    omega
  | logoutRequest inner =>
    simp only [encode, LogoutRequest.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 76 then (LoginRequestPacket.decode bytes).map fun (message, rest) => (.loginRequestPacket message, rest)
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).map fun (message, rest) => (.unsequencedDataPacket message, rest)
  else if tag = 82 then (ClientHeartbeat.decode bytes).map fun (message, rest) => (.clientHeartbeat message, rest)
  else if tag = 79 then (LogoutRequest.decode bytes).map fun (message, rest) => (.logoutRequest message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Soup Bin Tcp Packet -/
structure ClientSoupBinTcpPacket where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSoupBinTcpPacket

def encodeBody (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option (ClientSoupBinTcpPacket × List UInt8) := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let (clientPayload, bytes) ← ClientPayload.decode clientPacketType bytes
  pure ({ clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (ClientSoupBinTcpPacket × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ClientSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end ClientSoupBinTcpPacket

/-- Client Packet -/
structure ClientPacket where
  clientSoupBinTcpPacket : List ClientSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientSoupBinTcpPacket.encode message.clientSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientSoupBinTcpPacket ← decodeAll ClientSoupBinTcpPacket.decode bytes.length bytes
  pure { clientSoupBinTcpPacket }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.decode ClientSoupBinTcpPacket.decode_encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket _ (encodeMany_length_ge ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket), some_bind]
  rfl

end ClientPacket

end Omi.NasdaqNordicequitiesOrderentryOuchV5026Client
