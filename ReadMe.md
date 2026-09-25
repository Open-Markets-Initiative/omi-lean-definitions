# Omi Lean Definitions

Omi [Lean](https://lean-lang.org/ "The Lean theorem prover and programming language") definitions describe common binary exchange protocols as Lean 4 modules that carry their own proofs.


[![Lean](https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/About/Images/Lean.png)](https://lean-lang.org/)

These definitions are checked with the Lean toolchain: [lake](https://lean-lang.org/doc/reference/latest/ "The Lean language reference")
## Usage

Each .lean file is a self contained module for one protocol version: a structure per message, an inductive per coded field, a sum type dispatching on the message type, and the theorems relating each decoder to its encoder. The shared `Omi/Wire.lean` holds the field kinds (big and little endian integers, fixed width text, counted repetition) and their lemmas. Check every proof with lake:

```
lake build
```
A definition is used as an ordinary Lean library: `decode` reads a `List UInt8` and returns the message with the bytes that follow, `encode` writes one, and the theorems are available to anything built on top.

For toolchain information: [Lean Toolchain](https://lean-lang.org/install/ "Installing Lean")
## Development

Updates are greatly appreciated; however, this entire repository is source generated...including the words you are reading right now. If you wish to suggest definition updates, the recommended process is to create an issue with changes and explanation.  Time permitting, we will update the models and regenerate.

| Protocol Count | Generated Lines |
| --- | --- |
| 748 | 2492766 |

## Testing

[![Build](https://github.com/Open-Markets-Initiative/omi-lean-definitions/actions/workflows/build.yml/badge.svg)](https://github.com/Open-Markets-Initiative/omi-lean-definitions/actions/workflows/build.yml)

The build checks every proof. The tests under `.github/tests/` decode captured packets from [omi-data-packets](https://github.com/Open-Markets-Initiative/omi-data-packets "Omi Data Packets") and require each to be consumed exactly; each is a theorem decided at build time, so a failing test fails the build.

Please report any parsing errors as an [issue](https://github.com/Open-Markets-Initiative/omi-lean-definitions/issues "Omi Lean Issues").  Include a small note on the protocol and version, and a minimal capture demonstrating the problem. Also consider including a link or pdf specification documenting the correct behavior.

## Open Markets Initiative

[![Omi](https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/About/Images/Logo.png)](https://github.com/Open-Markets-Initiative/Directory)  The Open Markets Initiative (Omi) is a group of technologists dedicated to enhancing the stability of electronic financial markets using modern development methods.

Other generated code can be found at [Omi Projects](https://github.com/Open-Markets-Initiative/Directory/tree/main/Projects "Open Markets Initiative Projects"); for Omi rules and regulations, see [Omi Directory](https://github.com/Open-Markets-Initiative/Directory "Open Markets Initiative Directory").
## Organizations

> [24X][24X.Directory] · [A2X][A2X.Directory] · [Aquis][Aquis.Directory] · [Asx][Asx.Directory] · [B3][B3.Directory] · [Bist][Bist.Directory] · [Biva][Biva.Directory] · [BlueOceanAts][BlueOceanAts.Directory] · [Box][Box.Directory] · [BruceAts][BruceAts.Directory] · [Bse][Bse.Directory] · [CixAts][CixAts.Directory] · [Cme][Cme.Directory] · [Coinbase][Coinbase.Directory] · [Eurex][Eurex.Directory] · [Euronext][Euronext.Directory] · [Iex][Iex.Directory] · [Imperative][Imperative.Directory] · [Jpx][Jpx.Directory] · [Miax][Miax.Directory] · [Nasdaq][Nasdaq.Directory] · [Nse][Nse.Directory] · [Sgx][Sgx.Directory] · [SmallX][SmallX.Directory] · [Tmx][Tmx.Directory] · [Txse][Txse.Directory]

## Exchanges

> [24XEquities][24XEquities.Exchange] · [A2XEquities][A2XEquities.Exchange] · [AquisEquities][AquisEquities.Exchange] · [AsxDerivatives][AsxDerivatives.Exchange] · [AsxSecurities][AsxSecurities.Exchange] · [B3Derivatives][B3Derivatives.Exchange] · [BivaEquities][BivaEquities.Exchange] · [BlueEquities][BlueEquities.Ats] · [BorsaIstanbul][BorsaIstanbul.Exchange] · [BoxOptions][BoxOptions.Exchange] · [BruceEquities][BruceEquities.Ats] · [BseIndia][BseIndia.Exchange] · [CoinbaseDerivatives][CoinbaseDerivatives.Exchange] · [Deribit][Deribit.Exchange] · [EmeraldOptions][EmeraldOptions.Exchange] · [FseEquities][FseEquities.Exchange] · [GemxOptions][GemxOptions.Exchange] · [IexEquities][IexEquities.Exchange] · [IntelligentCross][IntelligentCross.Ats] · [IseOptions][IseOptions.Exchange] · [MiaxOptions][MiaxOptions.Exchange] · [MrxOptions][MrxOptions.Exchange] · [Mx][Mx.Exchange] · [NomOptions][NomOptions.Exchange] · [NordicEquities][NordicEquities.Exchange] · [NseCd][NseCd.Exchange] · [NseCm][NseCm.Exchange] · [NseCom][NseCom.Exchange] · [NseEquities][NseEquities.Exchange] · [NseFo][NseFo.Exchange] · [NsmEquities][NsmEquities.Exchange] · [NtxEquities][NtxEquities.Exchange] · [NtxOptions][NtxOptions.Exchange] · [OnyxFutures][OnyxFutures.Exchange] · [OseDerivatives][OseDerivatives.Exchange] · [PearlEquities][PearlEquities.Exchange] · [PearlOptions][PearlOptions.Exchange] · [PhlxOptions][PhlxOptions.Exchange] · [PsxEquities][PsxEquities.Exchange] · [SapphireOptions][SapphireOptions.Exchange] · [SmallFutures][SmallFutures.Exchange] · [SseEquities][SseEquities.Exchange] · [TseEquities][TseEquities.Exchange] · [Tsx][Tsx.Exchange] · [TsxAlpha][TsxAlpha.Exchange] · [TxseEquities][TxseEquities.Exchange]

## Platforms

> [CixAts CixAspen][CixAspen.Platform] · [Cme Globex][Globex.Platform] · [Euronext Optiq][Optiq.Platform] · [Eurex T7][T7.Platform] · [Sgx TitanDt][TitanDt.Platform]

## Consolidators

> [Uqdf][Uqdf.Consolidator] · [Utdf][Utdf.Consolidator] · [Utp][Utp.Consolidator]

## Related Definitions

The Open Markets Initiative provides protocol definitions in several formats:

- [Kaitai Struct Definitions][Kaitai.Definitions.Repository] — cross language binary parsers with the kaitai struct compiler
- [DFDL Definitions][Dfdl.Definitions.Repository] — declarative DFDL schemas for cross language parsing
- [P4 Definitions][P4.Definitions.Repository] — P4 programs for software and hardware data planes
- [Spicy Definitions][Spicy.Definitions.Repository] — declarative Spicy grammars for the spicy toolchain and the zeek network security monitor
- [TLA+ Definitions][Tla.Definitions.Repository] — TLA+ modules whose encode and decode are model checked with TLC
- [FIX Dictionaries][Fix.Dictionaries.Repository] — QuickFIX format xml data dictionaries, one per FIX version
- [Xml Specifications][Xml.Specifications.Repository] — the exchange protocol specification xmls, matching the original files
## Disclaimer

Any similarities between existing people, places and/or protocols is purely incidental.

Enjoy.

[Omi Projects]: https://github.com/Open-Markets-Initiative/Directory/tree/main/Projects "Open Markets Initiative Projects"
[Omi Rules and Regulations]: https://github.com/Open-Markets-Initiative/Directory/tree/main/License "Open Markets Initiative Rules and Regulations"

[Omi.Glossary.Testing]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Glossary/Testing.md "Protocol Testing Status"
[Omi.Glossary.Testing.Verified]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Glossary/Testing.md "Testing Status: Protocol has been tested on live data"
[Omi.Glossary.Testing.Incomplete]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Glossary/Testing.md "Testing Status: Protocol has been tested on live data but contains known issues"
[Omi.Glossary.Testing.Beta]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Glossary/Testing.md "Testing Status: Protocol has not been tested and structure is speculative"
[Omi.Glossary.Testing.Untested]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Glossary/Testing.md "Testing Status: Protocol has not been tested on live data"
[Omi.Glossary.Testing.Unavailable]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Glossary/Testing.md "Testing Status: Protocol does not state a testing status"
[Omi.Encoding.Definitions]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Protocols/ReadMe.md "Encoding Directory"

[Omi.Encoding.Sbe]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Sbe.md "Sbe Encoding"
[Omi.Encoding.Amd]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Amd.md "Amd Encoding"
[Omi.Encoding.Atp]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Atp.md "Atp Encoding"
[Omi.Encoding.Itch]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Itch.md "Itch Encoding"
[Omi.Encoding.Ouch]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Ouch.md "Ouch Encoding"
[Omi.Encoding.Glimpse]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Glimpse.md "Glimpse Encoding"
[Omi.Encoding.Udp]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Udp.md "Udp Encoding"
[Omi.Encoding.Hsvf]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Hsvf.md "Hsvf Encoding"
[Omi.Encoding.Sail]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Sail.md "Sail Encoding"
[Omi.Encoding.Atr]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Atr.md "Atr Encoding"
[Omi.Encoding.Fbe]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Fbe.md "Fbe Encoding"
[Omi.Encoding.Aspen]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Aspen.md "Aspen Encoding"
[Omi.Encoding.TcpOut]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/TcpOut.md "TcpOut Encoding"
[Omi.Encoding.Tcp]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Tcp.md "Tcp Encoding"
[Omi.Encoding.IexTp]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/IexTp.md "IexTp Encoding"
[Omi.Encoding.Flex]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Flex.md "Flex Encoding"
[Omi.Encoding.Mach]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Mach.md "Mach Encoding"
[Omi.Encoding.Fei]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Fei.md "Fei Encoding"
[Omi.Encoding.Meo]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Meo.md "Meo Encoding"
[Omi.Encoding.ESesM]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/ESesM.md "ESesM Encoding"
[Omi.Encoding.Utp]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Utp.md "Utp Encoding"
[Omi.Encoding.Binary]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Binary.md "Binary Encoding"
[Omi.Encoding.NnfTrimmed]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/NnfTrimmed.md "NnfTrimmed Encoding"
[Omi.Encoding.Xmt]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Xmt.md "Xmt Encoding"

[24X.24XEquities.Memo]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/24X/Protocols/24XEquities/Memo.md "Members Orders"
[24X.24XEquities.MemoirDepthFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/24X/Protocols/24XEquities/MemoirDepthFeed.md "Member Order Information Record Depth Feed"
[24X.24XEquities.MemoirLastSale]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/24X/Protocols/24XEquities/MemoirLastSale.md "Member Order Information Record Last Sale"
[24X.24XEquities.MemoirTopOfBook]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/24X/Protocols/24XEquities/MemoirTopOfBook.md "Member Order Information Record Top Of Book"
[A2X.A2XEquities.Rtmdf]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/A2X/Protocols/A2XEquities/Rtmdf.md "Real Time Market Data Feed"
[A2X.A2XEquities.Snapshot]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/A2X/Protocols/A2XEquities/Snapshot.md "Snapshot Feed"
[A2X.A2XEquities.UdpHeader]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/A2X/Protocols/A2XEquities/UdpHeader.md "Udp Headers"
[Aquis.AquisEquities.RealTime]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Aquis/Protocols/AquisEquities/RealTime.md "Real Time Market Data Feed"
[Aquis.AquisEquities.Replay]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Aquis/Protocols/AquisEquities/Replay.md "Market Data Replay"
[Aquis.AquisEquities.Snapshot]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Aquis/Protocols/AquisEquities/Snapshot.md "Aquis Market Data Snapshot"
[Aquis.AquisEquities.TcpHeader]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Aquis/Protocols/AquisEquities/TcpHeader.md "Tcp Headers"
[Aquis.AquisEquities.TradingProtocol]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Aquis/Protocols/AquisEquities/TradingProtocol.md "Aquis Trading Protocol"
[Aquis.AquisEquities.UdpHeader]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Aquis/Protocols/AquisEquities/UdpHeader.md "Udp Headers"
[Asx.AsxDerivatives.Ntp]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Asx/Protocols/AsxDerivatives/Ntp.md "New Trading Platform"
[Asx.AsxDerivatives.T24]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Asx/Protocols/AsxDerivatives/T24.md "24 Itch"
[Asx.AsxSecurities.Trade]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Asx/Protocols/AsxSecurities/Trade.md "Asx Trade"
[B3.B3Derivatives.BinaryEntryPoint]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/B3/Protocols/B3Derivatives/BinaryEntryPoint.md "Binary Entry Point"
[B3.B3Derivatives.BinaryUmdf]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/B3/Protocols/B3Derivatives/BinaryUmdf.md "Binary Unified Market Data Feed"
[Bist.BorsaIstanbul.GeniumInet]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Bist/Protocols/BorsaIstanbul/GeniumInet.md "Genium Inet"
[Biva.BivaEquities.Basic]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Biva/Protocols/BivaEquities/Basic.md "Basic"
[Biva.BivaEquities.Index]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Biva/Protocols/BivaEquities/Index.md "Index"
[Biva.BivaEquities.LastSale]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Biva/Protocols/BivaEquities/LastSale.md "Last Sale"
[Biva.BivaEquities.News]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Biva/Protocols/BivaEquities/News.md "News"
[Biva.BivaEquities.OrderEntry]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Biva/Protocols/BivaEquities/OrderEntry.md "Order Entry"
[Biva.BivaEquities.TotalView]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Biva/Protocols/BivaEquities/TotalView.md "Total View"
[BlueOceanAts.BlueEquities.Memo]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/BlueOceanAts/Protocols/BlueEquities/Memo.md "Members Orders"
[BlueOceanAts.BlueEquities.MemoirDepthFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/BlueOceanAts/Protocols/BlueEquities/MemoirDepthFeed.md "Member Order Information Record Depth Feed"
[BlueOceanAts.BlueEquities.MemoirLastSale]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/BlueOceanAts/Protocols/BlueEquities/MemoirLastSale.md "Member Order Information Record Last Sale"
[BlueOceanAts.BlueEquities.MemoirTopOfBook]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/BlueOceanAts/Protocols/BlueEquities/MemoirTopOfBook.md "Member Order Information Record Top Of Book"
[BlueOceanAts.CommonHeader]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/BlueOceanAts/Protocols/CommonHeader.md "Common Header"
[Box.BoxOptions.SolaMulticast]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Box/Protocols/BoxOptions/SolaMulticast.md "Sola Multicast"
[Box.BoxOptions.SolaOrderEntry]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Box/Protocols/BoxOptions/SolaOrderEntry.md "Sola Order Entry"
[Box.BoxOptions.SolaTradeReporting]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Box/Protocols/BoxOptions/SolaTradeReporting.md "Sola Trade Reporting"
[Box.BoxOptions.SolaUnicast]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Box/Protocols/BoxOptions/SolaUnicast.md "Sola Unicast"
[BruceAts.BruceEquities.BestBidAndOffer]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/BruceAts/Protocols/BruceEquities/BestBidAndOffer.md "Best Bid And Offer"
[BruceAts.BruceEquities.DepthOfBook]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/BruceAts/Protocols/BruceEquities/DepthOfBook.md "Depth Of Book"
[BruceAts.BruceEquities.LastSale]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/BruceAts/Protocols/BruceEquities/LastSale.md "Last Sale"
[Bse.BseIndia.Eobi]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Bse/Protocols/BseIndia/Eobi.md "Enhanced Order Book Interface"
[Bse.BseIndia.Eti]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Bse/Protocols/BseIndia/Eti.md "Enhanced Trading Interface"
[CixAts.CixAspen.MarketDataFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/CixAts/Protocols/CixAspen/MarketDataFeed.md "CIX Market Data Feed"
[CixAts.CixAspen.Rerequest]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/CixAts/Protocols/CixAspen/Rerequest.md "CIX Udp Rerequest"
[CixAts.CixAspen.Snapshot]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/CixAts/Protocols/CixAspen/Snapshot.md "CIX Tcp Snapshot"
[Cme.Globex.BrokerTecUst]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Cme/Protocols/Globex/BrokerTecUst.md "BrokerTec Us Treasuries"
[Cme.Globex.Derived]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Cme/Protocols/Globex/Derived.md "Derived Market Data"
[Cme.Globex.EbsSpectrum]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Cme/Protocols/Globex/EbsSpectrum.md "Ebs Spectrum Market Data"
[Cme.Globex.iLink3]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Cme/Protocols/Globex/iLink3.md "iLink 3"
[Cme.Globex.Mdp3]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Cme/Protocols/Globex/Mdp3.md "Market Data Platform 3"
[Cme.Globex.Settlements]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Cme/Protocols/Globex/Settlements.md "Settlements"
[Cme.Globex.Streamlined]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Cme/Protocols/Globex/Streamlined.md "Streamlined Market Data"
[Coinbase.CoinbaseDerivatives.MarketDataApi]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Coinbase/Protocols/CoinbaseDerivatives/MarketDataApi.md "Market Data Api"
[Coinbase.CoinbaseDerivatives.OrdersApi]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Coinbase/Protocols/CoinbaseDerivatives/OrdersApi.md "Orders Api"
[Coinbase.CoinbaseDerivatives.Session]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Coinbase/Protocols/CoinbaseDerivatives/Session.md "Session Layer"
[Coinbase.Deribit.MarketDataApi]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Coinbase/Protocols/Deribit/MarketDataApi.md "Market Data Api"
[Coinbase.Deribit.OrdersApi]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Coinbase/Protocols/Deribit/OrdersApi.md "Orders Api"
[Eurex.T7.Edci]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Eurex/Protocols/T7/Edci.md "Extended Derivatives Clearing Interface"
[Eurex.T7.Eobi]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Eurex/Protocols/T7/Eobi.md "Enhanced Order Book Interface"
[Eurex.T7.Eti]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Eurex/Protocols/T7/Eti.md "Enhanced Trading Interface"
[Eurex.T7.Xti]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Eurex/Protocols/T7/Xti.md "Cash Enhanced Trading Interface"
[Euronext.Optiq.DropCopyGateway]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Euronext/Protocols/Optiq/DropCopyGateway.md "Drop Copy Gateway"
[Euronext.Optiq.MarketDataGateway]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Euronext/Protocols/Optiq/MarketDataGateway.md "Market Data Gateway"
[Euronext.Optiq.OrderEntryGateway]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Euronext/Protocols/Optiq/OrderEntryGateway.md "Order Entry Gateway"
[Iex.IexEquities.Deep]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Iex/Protocols/IexEquities/Deep.md "Depth Of Book"
[Iex.IexEquities.DeepPlus]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Iex/Protocols/IexEquities/DeepPlus.md "DeepPlus"
[Iex.IexEquities.Tops]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Iex/Protocols/IexEquities/Tops.md "Top Of Book"
[Imperative.IntelligentCross.DepthOfBook]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Imperative/Protocols/IntelligentCross/DepthOfBook.md "Depth Of Book"
[Jpx.FseEquities.MarketByOrder]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Jpx/Protocols/FseEquities/MarketByOrder.md "Market By Order"
[Jpx.NseEquities.MarketByOrder]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Jpx/Protocols/NseEquities/MarketByOrder.md "Market By Order"
[Jpx.OseDerivatives.GeniumInet]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Jpx/Protocols/OseDerivatives/GeniumInet.md "Genium Inet"
[Jpx.SseEquities.MarketByOrder]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Jpx/Protocols/SseEquities/MarketByOrder.md "Market By Order"
[Jpx.TseEquities.MarketByOrder]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Jpx/Protocols/TseEquities/MarketByOrder.md "Market By Order"
[Miax.EmeraldOptions.Ais]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/EmeraldOptions/Ais.md "Administrative Information Subscriber"
[Miax.EmeraldOptions.ComplexTopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/EmeraldOptions/ComplexTopOfMarket.md "Complex Top of Market"
[Miax.EmeraldOptions.OrderFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/EmeraldOptions/OrderFeed.md "Order Feed"
[Miax.EmeraldOptions.TopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/EmeraldOptions/TopOfMarket.md "Top of Market"
[Miax.MiaxOptions.Ais]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/MiaxOptions/Ais.md "Administrative Information Subscriber"
[Miax.MiaxOptions.ComplexTopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/MiaxOptions/ComplexTopOfMarket.md "Complex Top Of Market"
[Miax.MiaxOptions.Mpf]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/MiaxOptions/Mpf.md "MIAX Product Feed"
[Miax.MiaxOptions.OrderFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/MiaxOptions/OrderFeed.md "Order Feed"
[Miax.MiaxOptions.TopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/MiaxOptions/TopOfMarket.md "Top of Market"
[Miax.OnyxFutures.DepthOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/OnyxFutures/DepthOfMarket.md "Depth Of Market"
[Miax.OnyxFutures.ExpressInterface]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/OnyxFutures/ExpressInterface.md "Express Interface"
[Miax.OnyxFutures.HeaderOnly]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/OnyxFutures/HeaderOnly.md "Headers Only"
[Miax.OnyxFutures.TopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/OnyxFutures/TopOfMarket.md "Top Of Market"
[Miax.PearlEquities.DepthOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/PearlEquities/DepthOfMarket.md "Depth Of Market"
[Miax.PearlEquities.ExpressOrders]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/PearlEquities/ExpressOrders.md "Express Orders"
[Miax.PearlEquities.HeaderOnly]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/PearlEquities/HeaderOnly.md "Headers Only"
[Miax.PearlEquities.TopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/PearlEquities/TopOfMarket.md "Top Of Market"
[Miax.PearlOptions.LiquidityFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/PearlOptions/LiquidityFeed.md "Liquidity Feed"
[Miax.PearlOptions.TopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/PearlOptions/TopOfMarket.md "Top Of Market"
[Miax.SapphireOptions.ComplexTopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/SapphireOptions/ComplexTopOfMarket.md "Complex Top of Market"
[Miax.SapphireOptions.LiquidityFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/SapphireOptions/LiquidityFeed.md "Liquidity Feed"
[Miax.SapphireOptions.TopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Miax/Protocols/SapphireOptions/TopOfMarket.md "Top of Market"
[Nasdaq.GemxOptions.DepthOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/GemxOptions/DepthOfMarket.md "Depth Of Market"
[Nasdaq.GemxOptions.OrderFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/GemxOptions/OrderFeed.md "Order Feed"
[Nasdaq.GemxOptions.TopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/GemxOptions/TopOfMarket.md "Top Of Market"
[Nasdaq.GemxOptions.TradeFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/GemxOptions/TradeFeed.md "Trade Feed"
[Nasdaq.IseOptions.DepthOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/IseOptions/DepthOfMarket.md "Depth Of Market"
[Nasdaq.IseOptions.OrderComboFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/IseOptions/OrderComboFeed.md "Ise Order Combo Market Data Feed"
[Nasdaq.IseOptions.OrderFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/IseOptions/OrderFeed.md "Ise Order Feed Market Data"
[Nasdaq.IseOptions.SpreadDepthOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/IseOptions/SpreadDepthOfMarket.md "Phlx Options Spread Depth"
[Nasdaq.IseOptions.SpreadOrders]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/IseOptions/SpreadOrders.md "Phlx Options Spread Orders"
[Nasdaq.IseOptions.SpreadTopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/IseOptions/SpreadTopOfMarket.md "Phlx Options Spread Top Of Market"
[Nasdaq.IseOptions.SpreadTradeFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/IseOptions/SpreadTradeFeed.md "Phlx Options Spread Trade Feed"
[Nasdaq.IseOptions.TopComboQuoteFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/IseOptions/TopComboQuoteFeed.md "Ise Top Combo Quote Feed"
[Nasdaq.IseOptions.TopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/IseOptions/TopOfMarket.md "Top Of Market"
[Nasdaq.IseOptions.TradeFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/IseOptions/TradeFeed.md "Trade Feed"
[Nasdaq.MrxOptions.DepthOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/MrxOptions/DepthOfMarket.md "Depth Of Market"
[Nasdaq.MrxOptions.OrderFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/MrxOptions/OrderFeed.md "Order Feed"
[Nasdaq.MrxOptions.SpreadDepthOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/MrxOptions/SpreadDepthOfMarket.md "Phlx Options Spread Depth"
[Nasdaq.MrxOptions.SpreadOrders]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/MrxOptions/SpreadOrders.md "Phlx Options Spread Orders"
[Nasdaq.MrxOptions.SpreadTopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/MrxOptions/SpreadTopOfMarket.md "Phlx Options Spread Top Of Market"
[Nasdaq.MrxOptions.SpreadTradeFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/MrxOptions/SpreadTradeFeed.md "Phlx Options Spread Trade Feed"
[Nasdaq.MrxOptions.TopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/MrxOptions/TopOfMarket.md "Top Of Market"
[Nasdaq.MrxOptions.TradeFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/MrxOptions/TradeFeed.md "Trade Feed"
[Nasdaq.NomOptions.Bono]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NomOptions/Bono.md "Nom Binary Order Entry"
[Nasdaq.NomOptions.Itto]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NomOptions/Itto.md "Itch To Trade Options"
[Nasdaq.NordicEquities.LastSale]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NordicEquities/LastSale.md "Nordic Equity Last Sale"
[Nasdaq.NordicEquities.OrderEntry]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NordicEquities/OrderEntry.md "Nordic Ouch 5 Order Entry"
[Nasdaq.NordicEquities.TotalView]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NordicEquities/TotalView.md "Nordic Equity TotalView"
[Nasdaq.NsmEquities.Aggregated]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NsmEquities/Aggregated.md "TotalView Aggregated"
[Nasdaq.NsmEquities.Level2]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NsmEquities/Level2.md "Level 2"
[Nasdaq.NsmEquities.NlsPlus]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NsmEquities/NlsPlus.md "Last Sale Plus"
[Nasdaq.NsmEquities.Nois]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NsmEquities/Nois.md "Net Order Imbalance Snapshot"
[Nasdaq.NsmEquities.NoiView]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NsmEquities/NoiView.md "Net Order Imbalance View"
[Nasdaq.NsmEquities.Orders]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NsmEquities/Orders.md "Orders"
[Nasdaq.NsmEquities.Qbbo]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NsmEquities/Qbbo.md "Quoted Best Bid And Offer"
[Nasdaq.NsmEquities.TotalView]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NsmEquities/TotalView.md "TotalView Itch"
[Nasdaq.NtxEquities.Orders]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NtxEquities/Orders.md "BX Orders"
[Nasdaq.NtxEquities.Qbbo]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NtxEquities/Qbbo.md "Quoted Best Bid And Offer"
[Nasdaq.NtxEquities.TotalView]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NtxEquities/TotalView.md "TX TotalView Itch"
[Nasdaq.NtxOptions.DepthOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NtxOptions/DepthOfMarket.md "Depth Of Market"
[Nasdaq.NtxOptions.TopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NtxOptions/TopOfMarket.md "Top Of Market"
[Nasdaq.NtxOptions.TradeFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NtxOptions/TradeFeed.md "Trade Feed"
[Nasdaq.PhlxOptions.DepthOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PhlxOptions/DepthOfMarket.md "Depth Of Market"
[Nasdaq.PhlxOptions.Orders]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PhlxOptions/Orders.md "PHLX Orders"
[Nasdaq.PhlxOptions.SpreadDepthOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PhlxOptions/SpreadDepthOfMarket.md "Spread Depth"
[Nasdaq.PhlxOptions.SpreadOrders]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PhlxOptions/SpreadOrders.md "Spread Orders"
[Nasdaq.PhlxOptions.SpreadTopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PhlxOptions/SpreadTopOfMarket.md "Spread Top Of Market"
[Nasdaq.PhlxOptions.SpreadTradeFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PhlxOptions/SpreadTradeFeed.md "Spread Trade Feed"
[Nasdaq.PhlxOptions.TopOfMarket]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PhlxOptions/TopOfMarket.md "Top Of Market"
[Nasdaq.PhlxOptions.TradeFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PhlxOptions/TradeFeed.md "Trade Feed"
[Nasdaq.PsxEquities.Bbo]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PsxEquities/Bbo.md "Best Bid And Offer"
[Nasdaq.PsxEquities.LastSale]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PsxEquities/LastSale.md "Last Sale"
[Nasdaq.PsxEquities.Orders]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PsxEquities/Orders.md "Orders"
[Nasdaq.PsxEquities.TotalView]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PsxEquities/TotalView.md "TotalView Itch"
[Nasdaq.Uqdf.Output]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/Uqdf/Output.md "Output"
[Nasdaq.Utdf.Output]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/Utdf/Output.md "Output"
[Nasdaq.Utp.Input]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/Utp/Input.md ""
[Nasdaq.Utp.Snapshot]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/Utp/Snapshot.md "Snapshot"
[Nse.NseCd.Mtbt]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseCd/Mtbt.md "Multicast Tick By Tick"
[Nse.NseCd.MtbtNdal]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseCd/MtbtNdal.md "Multicast Tick By Tick Data Feed"
[Nse.NseCd.Recovery]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseCd/Recovery.md "Mtbt Tick Data Recovery"
[Nse.NseCd.Snapshot]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseCd/Snapshot.md "Mtbt Order Book Snapshot Recovery"
[Nse.NseCm.Mtbt]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseCm/Mtbt.md "Multicast Tick By Tick"
[Nse.NseCm.MtbtNdal]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseCm/MtbtNdal.md "Multicast Tick By Tick Data Feed"
[Nse.NseCm.Recovery]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseCm/Recovery.md "Mtbt Tick Data Recovery"
[Nse.NseCm.Snapshot]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseCm/Snapshot.md "Mtbt Order Book Snapshot Recovery"
[Nse.NseCom.Mtbt]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseCom/Mtbt.md "Multicast Tick By Tick"
[Nse.NseCom.Recovery]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseCom/Recovery.md "Mtbt Tick Data Recovery"
[Nse.NseCom.Snapshot]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseCom/Snapshot.md "Mtbt Order Book Snapshot Recovery"
[Nse.NseFo.Mtbt]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseFo/Mtbt.md "Multicast Tick By Tick"
[Nse.NseFo.OrderEntry]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseFo/OrderEntry.md "Order Entry"
[Nse.NseFo.Recovery]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseFo/Recovery.md "Mtbt Tick Data Recovery"
[Nse.NseFo.Snapshot]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nse/Protocols/NseFo/Snapshot.md "Mtbt Order Book Snapshot Recovery"
[Sgx.TitanDt.DepthOfBook]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Sgx/Protocols/TitanDt/DepthOfBook.md "Depth Of Book"
[SmallX.SmallFutures.OrderBookFeed]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/SmallX/Protocols/SmallFutures/OrderBookFeed.md "Order Book Feed"
[Tmx.Mx.SolaMulticast]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Tmx/Protocols/Mx/SolaMulticast.md "Sola Multicast"
[Tmx.Tsx.QuantumFeedLevel1]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Tmx/Protocols/Tsx/QuantumFeedLevel1.md "Quantum Feed Level 1"
[Tmx.Tsx.QuantumFeedLevel2]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Tmx/Protocols/Tsx/QuantumFeedLevel2.md "Quantum Feed Level 2"
[Tmx.TsxAlpha.QuantumFeedLevel1]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Tmx/Protocols/TsxAlpha/QuantumFeedLevel1.md "Quantum Feed Level 1"
[Tmx.TsxAlpha.QuantumFeedLevel2]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Tmx/Protocols/TsxAlpha/QuantumFeedLevel2.md "Quantum Feed Level 2"
[Txse.TxseEquities.Framing]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Txse/Protocols/TxseEquities/Framing.md ""

[24X.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/24x "24 National Exchange"
[A2X.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/a2x "A2X Markets"
[Aquis.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/aquis "Aquis Exchange"
[Asx.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/asx "Australian Securities Exchange"
[B3.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/b3 "Brasil, Bolsa, Balcão"
[Bist.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/bist "Borsa İstanbul A.Ş."
[Biva.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/biva "Bolsa Institucional de Valores"
[BlueOceanAts.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/blueoceanats "Blue Ocean Technologies"
[Box.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/box "Box Options Market"
[BruceAts.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/bruceats "Bruce ATS"
[Bse.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/bse "BSE Limited"
[CixAts.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/cixats "CIX Trading Inc."
[Cme.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/cme "CME Group"
[Coinbase.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/coinbase "Coinbase"
[Eurex.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/eurex "Eurex Exchange"
[Euronext.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/euronext "Euronext"
[Iex.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/iex "Investors Exchange"
[Imperative.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/imperative "Imperative Execution"
[Jpx.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/jpx "Japan Exchange Group"
[Miax.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/miax "Miami International Holdings"
[Nasdaq.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq "National Association of Securities Dealers Automated Quotations (Nasdaq)"
[Nse.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nse "National Stock Exchange of India Ltd"
[Sgx.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/sgx "Singapore Exchange"
[SmallX.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/smallx "The Small Exchange"
[Tmx.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/tmx "TMX Group"
[Txse.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/txse "Texas Stock Exchange"

[24XEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/24x "24X Equities"
[A2XEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/a2x "A2X Equities"
[AquisEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/aquis "Aquis Equities"
[AsxDerivatives.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/asx/asxderivatives "Asx Derivatives"
[AsxSecurities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/asx/asxsecurities "Asx Securities"
[B3Derivatives.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/b3/b3derivatives "B3 Derivatives"
[BivaEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/biva/bivaequities "Biva Equities"
[BlueEquities.Ats]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/blueoceanats "Blue Equities"
[BorsaIstanbul.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/bist/borsaistanbul "Borsa Istanbul"
[BoxOptions.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/box/boxoptions "BOX Options Exchange"
[BruceEquities.Ats]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/bruceats "Bruce ATS Equities"
[BseIndia.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/bse/bseindia "BSE India"
[CixAspen.Platform]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/cixats "CIX Aspen"
[CoinbaseDerivatives.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/coinbase/coinbasederivatives "Coinbase Derivatives"
[Deribit.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/coinbase/deribit "Deribit"
[EmeraldOptions.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/miax/emeraldoptions "MIAX Emerald Options"
[FseEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/jpx/fseequities "Fukuoka Stock Exchange Equities"
[GemxOptions.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/gemxoptions "Nasdaq GEMX"
[Globex.Platform]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/cme/globex "CME Globex"
[IexEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/iex/iexequities "IEX Equities"
[IntelligentCross.Ats]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/imperative "Intelligent Cross"
[IseOptions.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/iseoptions "Nasdaq ISE"
[MiaxOptions.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/miax/miaxoptions "MIAX Options"
[MrxOptions.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/mrxoptions "Nasdaq MRX"
[Mx.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/tmx/mx "Montreal Exchange"
[NomOptions.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/nomoptions "Nasdaq Options Market"
[NordicEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/nordicequities "Nasdaq Nordic Equities"
[NseCd.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nse/nsecd "NSE Currency Derivatives"
[NseCm.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nse/nsecm "NSE Capital Market"
[NseCom.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nse/nsecom "NSE Commodity Derivatives"
[NseEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/jpx/nseequities "Nagoya Stock Exchange Equities"
[NseFo.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nse/nsefo "NSE Futures & Options"
[NsmEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/nsmequities "Nasdaq Stock Market"
[NtxEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/ntxequities "Nasdaq Texas"
[NtxOptions.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/ntxoptions "Nasdaq Texas Options"
[OnyxFutures.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/miax/onyxfutures "MIAX Futures Onyx"
[Optiq.Platform]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/euronext/optiq "Euronext Optiq"
[OseDerivatives.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/jpx/osederivatives "Osaka Securities Exchange"
[PearlEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/miax/pearlequities "MIAX Pearl Equities"
[PearlOptions.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/miax/pearloptions "MIAX Pearl Options"
[PhlxOptions.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/phlxoptions "Nasdaq PHLX"
[PsxEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/psxequities "Nasdaq PSX"
[SapphireOptions.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/miax/sapphireoptions "MIAX Sapphire Options"
[SmallFutures.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/smallx "Small Exchange"
[SseEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/jpx/sseequities "Sapporo Securities Exchange Equities"
[T7.Platform]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/eurex/t7 "T7"
[TitanDt.Platform]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/sgx/titandt "SGX Titan"
[TseEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/jpx/tseequities "Tokyo Stock Exchange Equities"
[Tsx.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/tmx/tsx "Toronto Stock Exchange"
[TsxAlpha.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/tmx/tsxalpha "TSX Alpha Exchange"
[TxseEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/txse/txseequities "Txse Equities"
[Uqdf.Consolidator]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/uqdf "Nasdaq UTP Quote Data Feed"
[Utdf.Consolidator]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/utdf "Nasdaq UTP Trade Data Feed"
[Utp.Consolidator]: https://github.com/Open-Markets-Initiative/omi-lean-definitions/tree/main/nasdaq/utp "Nasdaq Unlisted Trading Privileges Plan"

[Kaitai.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-kaitai-struct-definitions "Omi Kaitai Struct Definitions"
[Dfdl.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-dfdl-definitions "Omi DFDL Definitions"
[P4.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-p4-definitions "Omi P4 Definitions"
[Spicy.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-spicy-definitions "Omi Spicy Definitions"
[Tla.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-tla-definitions "Omi TLA+ Definitions"
[Fix.Dictionaries.Repository]: https://github.com/Open-Markets-Initiative/omi-fix-dictionaries "Omi FIX Dictionaries"
[Xml.Specifications.Repository]: https://github.com/Open-Markets-Initiative/omi-xml-specifications "Omi Xml Specifications"
