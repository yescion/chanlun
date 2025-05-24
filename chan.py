# -*- coding: utf-8 -*-

# 缠论分析系统
# 基于Python的缠论技术分析工具，用于股票市场趋势判断
# 包含完整的分型、笔、线段、中枢等分析功能，并提供网页可视化界面

import json
import math
import mmap
import time
import struct
import asyncio
import datetime
import traceback
import sys

from enum import Enum
from random import randint, choice
from pathlib import Path
from threading import Thread
from functools import wraps, lru_cache
from typing import List, Self, Optional, Tuple, final, Dict, Any, Set, Final, SupportsInt, Union, Literal # Add Literal
from abc import ABCMeta, abstractmethod

import requests
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
from fastapi import FastAPI, WebSocket, WebSocketDisconnect, Request, Query
from termcolor import colored
from collections import defaultdict

import os

from stock_data_handler import StockDataHandler

# __all__ = ["Line", "Bar", "Bi", "Duan", "ZhongShu", "FenXing", "BaseAnalyzer"]
SupportsHL = Union["Line", "Bar", "Bi", "Duan", "ZhongShu", "FenXing", "Interval", "Pillar"]

# 添加从字符串周期到秒数的映射
PERIOD_STRING_TO_SECONDS: Dict[str, int] = {
    "1m": 60,
    "3m": 180,
    "5m": 300,
    "15m": 900,
    "30m": 1800,
    "60m": 3600, # QMT 使用 60m 表示小时
    "1h": 3600,
    "2h": 7200,
    "4h": 14400,
    "6h": 21600,
    "12h": 43200,
    "1d": 86400,
    "1w": 604800,
    "1mon": 2592000, # 近似值
    # 根据需要添加更多 QMT 支持的周期及其秒数
}

def timer(func):
    """函数执行时间装饰器，用于性能分析"""
    @wraps(func)
    def wrapper_timer(*args, **kwargs):
        tic = time.perf_counter()
        value = func(*args, **kwargs)
        toc = time.perf_counter()
        elapsed_time = toc - tic
        print(f"Elapsed time: {elapsed_time:0.4f} seconds")
        return value

    return wrapper_timer


def ts2int(timestamp: str):
    """将时间字符串转换为时间戳整数"""
    return int(time.mktime(datetime.datetime.strptime(timestamp, "%Y-%m-%d %H:%M:%S").timetuple()))


def int2ts(timestamp: int):
    """将时间戳整数转换为时间字符串"""
    return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(int(timestamp)))


class Freq(Enum):
    """
    时间周期枚举类
    定义了各种交易周期，从秒级到天级别，值表示对应的秒数
    """
    # 60 180 300 900 1800 3600 7200 14400 21600 43200 86400 259200
    S1: int = 1         # 1秒
    S3: int = 3         # 3秒
    S5: int = 5         # 5秒
    S12: int = 12       # 12秒
    m1: int = 60 * 1    # 1分钟
    m3: int = 60 * 3    # 3分钟
    m5: int = 60 * 5    # 5分钟
    m15: int = 60 * 15  # 15分钟
    m30: int = 60 * 30  # 30分钟
    H1: int = 60 * 60 * 1  # 1小时
    H2: int = 60 * 60 * 2  # 2小时
    H4: int = 60 * 60 * 4  # 4小时
    H6: int = 60 * 60 * 6  # 6小时
    H12: int = 60 * 60 * 12  # 12小时
    D1: int = 60 * 60 * 24  # 1天
    D3: int = 60 * 60 * 24 * 3  # 3天

    def __int__(self):
        """返回周期对应的秒数"""
        return self.value


class Pillar:
    """
    柱体类，用于表示具有高低点的基本数据结构
    在缠论中通常用于表示缺口、价格区间等
    """
    __slots__ = "high", "low"

    def __init__(self, high: float, low: float):
        """
        初始化柱体对象
        
        Args:
            high: 高点价格
            low: 低点价格
        """
        assert high > low
        self.high = high
        self.low = low


class Shape(Enum):
    """
    形态枚举类
    定义了K线和分型的各种形态类型
    """
    D = "底分型"     # 底分型，表示局部最低点
    G = "顶分型"     # 顶分型，表示局部最高点
    S = "上升分型"   # 上升分型，表示持续上涨
    X = "下降分型"   # 下降分型，表示持续下跌
    T = "喇叭口型"   # 喇叭口型，表示价格区间逐渐扩大

    def __str__(self):
        """返回形态名称"""
        return self.name

    def __repr__(self):
        """返回形态名称的字符串表示"""
        return self.name


class Direction(Enum):
    """
    方向枚举类
    定义了K线走势的各种方向和关系
    是缠论分析中描述价格变化关系的核心概念
    """
    Up = "向上"          # 上涨，价格走高
    Down = "向下"        # 下跌，价格走低
    JumpUp = "缺口向上"   # 向上跳空，价格出现向上跳空缺口
    JumpDown = "缺口向下" # 向下跳空，价格出现向下跳空缺口
    NextUp = "连接向上"   # 高点与后一低点相同，表示连续上涨
    NextDown = "连接向下" # 低点与后一高点相同，表示连续下跌
    Left = "左包右"      # 顺序包含关系，左边的价格区间包含右边的
    Right = "右包左"     # 逆序包含关系，右边的价格区间包含左边的

    def __str__(self):
        """返回方向名称"""
        return self.name

    def __repr__(self):
        """返回方向名称的字符串表示"""
        return self.name

    def __int__(self):
        """
        返回方向的整数表示
        用于方向的数值化计算和比较
        """
        match self:
            case Direction.Up:
                return 1
            case Direction.Down:
                return -1
            case Direction.JumpUp:
                return 2
            case Direction.JumpDown:
                return -2
            case Direction.NextUp:
                return 3
            case Direction.NextDown:
                return -3
            case Direction.Left:
                return 7
            case Direction.Right:
                return 9

    def reversal(self) -> Self:
        """
        返回当前方向的反转方向
        用于方向反转的计算
        """
        match self:
            case Direction.Up:
                return Direction.Down
            case Direction.Down:
                return Direction.Up
            case Direction.JumpUp:
                return Direction.JumpDown
            case Direction.JumpDown:
                return Direction.JumpUp
            case Direction.NextUp:
                return Direction.NextDown
            case Direction.NextDown:
                return Direction.NextUp
            case Direction.Left:
                return Direction.Right
            case Direction.Right:
                return Direction.Left

    def is_down(self) -> bool:
        """判断是否为下降方向"""
        match self:
            case Direction.Down | Direction.JumpDown | Direction.NextDown:
                return True
            case _:
                return False

    def is_up(self) -> bool:
        """判断是否为上升方向"""
        match self:
            case Direction.Up | Direction.JumpUp | Direction.NextUp:
                return True
            case _:
                return False

    def is_jump(self) -> bool:
        """判断是否为跳空方向"""
        match self:
            case Direction.JumpDown | Direction.JumpUp:
                return True
            case _:
                return False

    def is_include(self) -> bool:
        """判断是否为包含关系"""
        match self:
            case Direction.Left | Direction.Right:
                return True
            case _:
                return False

    def is_next(self):
        """判断是否为连接关系"""
        match self:
            case Direction.NextUp | Direction.NextDown:
                return True
            case _:
                return False

    @staticmethod
    def generator(obj: int, directions):
        """
        生成指定数量的随机方向
        用于测试和模拟数据生成
        
        Args:
            obj: 生成数量
            directions: 可选的方向列表
        """
        i: int = obj
        while i >= 0:
            yield choice(directions)
            i -= 1


class ChanException(Exception):
    """缠论分析过程中的异常类，用于标识分析过程中的错误情况"""
    ...


def _print(*args, **kwords):
    """
    带颜色的打印函数
    根据不同的内容类型使用不同的颜色进行打印
    用于调试和可视化输出
    """
    result = []
    for i in args:
        if i in ("小阳", True, Shape.D, "底分型") or "小阳" in str(i):
            result.append(colored(i, "green"))

        elif i in ("老阳", False, Shape.G, "顶分型") or "老阳" in str(i):
            result.append(colored(i, "red"))

        elif i in ("少阴",) or "少阴" in str(i):
            result.append("\33[07m" + colored(i, "yellow"))

        elif i in ("老阴",) or "老阴" in str(i):
            result.append("\33[01m" + colored(i, "blue"))

        elif "PUSH" in str(i):
            result.append(colored(i, "red"))

        elif "POP" in str(i):
            result.append(colored(i, "green"))

        elif "ANALYSIS" in str(i):
            result.append(colored(i, "blue"))

        else:
            result.append(i)
    result = tuple(result)
    print(*result, **kwords)


def dp(*args, **kwords):
    """调试打印函数，可通过标志控制是否打印"""
    if not 1:
        _print(*args, **kwords)


def bdp(*args, **kwargs):
    """笔调试打印函数，可通过标志控制是否打印"""
    if not 1:
        dp(*args, **kwargs)


def ddp(*args, **kwargs):
    """段调试打印函数，可通过标志控制是否打印"""
    if not 0:
        dp(*args, **kwargs)


def zsdp(*args, **kwargs):
    """中枢调试打印函数，可通过标志控制是否打印"""
    if not 1:
        dp(*args, **kwargs)

def get_name(symbol):
    '''
    curl ^"https://push2.eastmoney.com/api/qt/stock/get?invt=2^&fltt=1^&cb=^&fields=f58^&secid=0.002484^&ut=fa5fd1943c7b386f172d6893dbfba10b^&wbp2u=^%^7C0^%^7C0^%^7C0^%^7Cweb^&dect=1^&_=1747648540692^" ^
    -H ^"Accept: text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7^" ^
    -H ^"Accept-Language: zh-CN,zh;q=0.9^" ^
    -H ^"Cache-Control: max-age=0^" ^
    -H ^"Connection: keep-alive^" ^
    -b ^"qgqp_b_id=bc56d3efaec1e1e5d1735f4a06197c82; HAList=ty-0-000837-^%^u79E6^%^u5DDD^%^u673A^%^u5E8A^%^2Cty-90-BK0482-^%^u5546^%^u4E1A^%^u767E^%^u8D27; fullscreengg=1; fullscreengg2=1; st_si=47951552693900; st_asi=delete; st_pvi=72690208904211; st_sp=2025-04-10^%^2013^%^3A17^%^3A02; st_inirUrl=https^%^3A^%^2F^%^2Fdata.eastmoney.com^%^2Fzjlx^%^2Fdetail.html; st_sn=2; st_psi=2025051917554169-113200301328-8533199523^" ^
    -H ^"Sec-Fetch-Dest: document^" ^
    -H ^"Sec-Fetch-Mode: navigate^" ^
    -H ^"Sec-Fetch-Site: none^" ^
    -H ^"Sec-Fetch-User: ?1^" ^
    -H ^"Upgrade-Insecure-Requests: 1^" ^
    -H ^"User-Agent: Mozilla/5.0 (X11; Linux aarch64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.0.0 Safari/537.36 CrKey/1.54.250320^"
    '''
    url = "https://push2.eastmoney.com/api/qt/stock/get"
    # 股票代码开头为00，ex=0, 股票代码开头为60，ex=1
    ex = 0 if symbol.startswith("sz") else 1
    params = {
        "invt": "2",
        "fltt": "1",
        "cb": "",
        "fields": "f58",
        "secid": f"{ex}.{symbol[2:]}",
        "ut": "fa5fd1943c7b386f172d6893dbfba10b",
        "wbp2u": "|0|0|0|0|web",
        "dect": "1",
        "_": int(time.time() * 1000)
    }
    print(params)
    headers = {
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7",
        "Accept-Language": "zh-CN,zh;q=0.9",
        "Cache-Control": "max-age=0",
        "Connection": "keep-alive",
        "Sec-Fetch-Dest": "document",
        "Sec-Fetch-Mode": "navigate",
        "Sec-Fetch-Site": "none",
        "Sec-Fetch-User": "?1",
        "Upgrade-Insecure-Requests": "1",
        "User-Agent": "Mozilla/5.0 (X11; Linux aarch64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.0.0 Safari/537.36 CrKey/1.54.250320"
    }
    response = requests.get(url, params=params, headers=headers)
    response.raise_for_status()
    data = response.json()
    print(data)
    return data["data"]["f58"]

@lru_cache(maxsize=128)
def double_relation(left: SupportsHL, right: SupportsHL) -> Direction:
    """
    判断两个带有[low, high]属性对象之间的关系
    这是缠论分析中的核心函数之一，用于确定两个价格区间的关系
    
    Args:
        left: 左侧对象
        right: 右侧对象
    
    Returns:
        Direction: 两对象之间的关系，包括上涨、下跌、跳涨、跳跌、包含等
    """
    relation = None
    assert left is not right, ChanException("相同对象无法比较", left, right)

    if (left.low <= right.low) and (left.high >= right.high):
        relation = Direction.Left  # "左包右" # 顺序

    elif (left.low >= right.low) and (left.high <= right.high):
        relation = Direction.Right  # "右包左" # 逆序

    elif (left.low < right.low) and (left.high < right.high):
        relation = Direction.Up  # "上涨"
        if left.high < right.low:
            relation = Direction.JumpUp  # "跳涨"

        if left.high == right.low:
            relation = Direction.NextUp

    elif (left.low > right.low) and (left.high > right.high):
        relation = Direction.Down  # "下跌"
        if left.low > right.high:
            relation = Direction.JumpDown  # "跳跌"
        if left.low == right.high:
            relation = Direction.NextDown

    return relation


def triple_relation(left: SupportsHL, mid: SupportsHL, right: SupportsHL, use_right: bool = False, ignore: bool = False) -> tuple[Optional[Shape], tuple[Direction, Direction], Optional[Pillar]]:
    """
    判断三个对象之间的关系，用于确定分型
    缠论分析中判断顶底分型的核心函数
    
    Args:
        left: 左侧对象
        mid: 中间对象
        right: 右侧对象
        use_right: 是否使用右侧包含关系
        ignore: 是否忽略包含关系错误
    
    Returns:
        tuple: 包含三个元素:
            1. Shape: 分型形态（顶分型、底分型、上升分型、下降分型或喇叭口型）
            2. tuple[Direction, Direction]: 左中和中右的关系
            3. Optional[Pillar]: 如果有重叠区间，返回重叠柱体
    """
    if any((left == mid, mid == right, left == right)):
        raise ChanException("相同对象无法比较")

    zg = min(left.high, mid.high, right.high)
    zd = max(left.low, mid.low, right.low)
    if zg > zd:
        pillar = Pillar(high=zg, low=zd)
    else:
        pillar = None

    shape = None
    lm = double_relation(left, mid)
    mr = double_relation(mid, right)
    # lr = double_relation(left, right)
    match (lm, mr):
        case (Direction.Left, _):
            if ignore:
                ...  # print("顺序包含 lm", left, mid)
            else:
                raise ChanException("顺序包含 lm", left, mid)
        case (_, Direction.Left):
            if ignore:
                ...  # print("顺序包含 mr", mid, right)
            else:
                raise ChanException("顺序包含 mr", mid, right)

        case (Direction.Up | Direction.JumpUp | Direction.NextUp, Direction.Up | Direction.JumpUp | Direction.NextUp):
            shape = Shape.S
        case (Direction.Up | Direction.JumpUp | Direction.NextUp, Direction.Down | Direction.JumpDown | Direction.NextDown):
            shape = Shape.G
        case (Direction.Up | Direction.JumpUp | Direction.NextUp, Direction.Right) if use_right:
            shape = Shape.S

        case (Direction.Down | Direction.JumpDown | Direction.NextDown, Direction.Up | Direction.JumpUp | Direction.NextUp):
            shape = Shape.D
        case (Direction.Down | Direction.JumpDown | Direction.NextDown, Direction.Down | Direction.JumpDown | Direction.NextDown):
            shape = Shape.X
        case (Direction.Down | Direction.JumpDown | Direction.NextDown, Direction.Right) if use_right:
            shape = Shape.X

        case (Direction.Right, Direction.Up | Direction.JumpUp | Direction.NextUp) if use_right:
            shape = Shape.D
        case (Direction.Right, Direction.Down | Direction.JumpDown | Direction.NextDown) if use_right:
            shape = Shape.G
        case (Direction.Right, Direction.Right) if use_right:
            shape = Shape.T
        case _:
            print("未匹配的关系", use_right, lm, mr)

    if shape is None:
        ...  # print(colored("triple_relation: ", "red"), shape, (lm, mr), left, mid, right)

    return shape, (lm, mr), pillar


class Command:
    """
    命令类，表示对数据的操作类型
    用于Observer模式中传递操作信息
    """
    APPEND: Final[str] = "APPEND"   # 添加操作
    MODIFY: Final[str] = "MODIFY"   # 修改操作
    REMOVE: Final[str] = "REMOVE"   # 删除操作

    def __init__(self, cmd: str, info: str) -> None:
        """
        初始化命令对象
        
        Args:
            cmd: 命令类型 (APPEND/MODIFY/REMOVE)
            info: 命令相关的信息
        """
        self.cmd = cmd
        self.info = info

    def __str__(self):
        # return f"{self.cmd.upper()}({self.info})"
        return f"{self.cmd.upper()}"

    @classmethod
    def Append(cls, stamp: str) -> Self:
        """创建添加命令"""
        return Command(cls.APPEND, stamp)

    @classmethod
    def Modify(cls, stamp: str) -> Self:
        """创建修改命令"""
        return Command(cls.MODIFY, stamp)

    @classmethod
    def Remove(cls, stamp: str) -> Self:
        """创建删除命令"""
        return Command(cls.REMOVE, stamp)


@final
class BSPoint:
    """
    买卖点类，用于标记缠论系统中的交易信号点
    包括一二三类买卖点信息
    """
    __slots__ = "info", "tp", "dt", "price", "valid", "creation_offset", "fix_offset", "stamp"

    def __init__(self, info: str, tp: str, dt: datetime, price: float, valid: bool, creation_offset: int, fix_offset: int, stamp: str) -> None:
        """
        初始化买卖点对象
        
        Args:
            info: 信号来源 ('Bi' 或 'Duan')
            tp: 买卖点类型 ('FirstBuy', 'SecondBuy', 'ThirdBuy', 'FirstSell', 'SecondSell', 'ThirdSell')
            dt: 买卖点的日期时间
            price: 买卖点的价格
            valid: 买卖点是否有效
            creation_offset: 创建该买卖点的线的索引
            fix_offset: 固定该买卖点的线的索引
            stamp: 唯一标识符
        """
        self.info = info # 'Bi' or 'Duan'
        self.tp = tp     # 'FirstBuy', 'SecondBuy', 'ThirdBuy', 'FirstSell', 'SecondSell', 'ThirdSell'
        self.dt = dt
        self.price = price
        self.valid = valid # Indicates if the point is still considered valid
        self.creation_offset = creation_offset # Index of the line that created this point
        self.fix_offset = fix_offset # Index of the line where the point is finally fixed (can be same as creation)
        self.stamp = stamp # Unique stamp for identification


class ZShuCondition(Enum):
    """
    中枢条件枚举类
    定义了中枢的三种变化情况
    在缠论中用于确定中枢的形成、延续和扩张
    """

    New: str = "新生"       # 新生中枢，首次形成的中枢
    Continue: str = "延续"  # 延续中枢，在原有中枢范围内继续发展
    Expand: str = "扩张"    # 扩张中枢，突破原有中枢范围形成新中枢


@final
class ChanConfig:
    """
    缠论配置类
    定义了缠论分析系统的各种参数和开关
    包括笔、线段、中枢的计算规则和技术指标配置
    """
    __slots__ = (
        "ANALYZER_CALC_BI",
        "ANALYZER_CALC_BI_ZS",
        "ANALYZER_CALC_XD",
        "ANALYZER_CALC_XD_ZS",
        "ANALYZER_SHON_TV",
        "BI_LASTorFIRST",
        "BI_FENGXING",
        "BI_JUMP",
        "BI_JUMP_SCALE",
        "BI_LENGTH",
        "MACD_FAST_PERIOD",
        "MACD_SIGNAL_PERIOD",
        "MACD_SLOW_PERIOD",
        "ANALYZER_CALC_MACD",
    )

    def __init__(self):
        """初始化默认的缠论配置参数"""
        self.BI_LENGTH = 5  # 成BI最低长度，即一笔至少需要的K线数量
        self.BI_JUMP = True  # 跳空是否判定为 NewBar，即跳空能否构成分型的一部分
        self.BI_JUMP_SCALE = 0.15  # 当跳空判定为NewBar时，此值大于0时按照缺口所占比例判定是否为NewBar，等于0时直接判定
        self.BI_LASTorFIRST = True  # 一笔终点存在多个终点时 True: 取最后一个, False: 取第一个
        self.BI_FENGXING = False  # True: 一笔起始分型高低包含整支笔则不成笔, False: 只判断分型中间数据是否包含

        self.ANALYZER_CALC_BI = True  # 是否计算笔
        self.ANALYZER_CALC_XD = True  # 是否计算线段
        self.ANALYZER_CALC_BI_ZS = True  # 是否计算笔中枢
        self.ANALYZER_CALC_XD_ZS = True  # 是否计算线段中枢
        self.ANALYZER_CALC_MACD = True  # 是否计算MACD指标
        self.ANALYZER_SHON_TV = True  # 是否在TradingView中显示分析结果
        self.MACD_FAST_PERIOD = 12.0  # MACD快线周期参数
        self.MACD_SLOW_PERIOD = 26.0  # MACD慢线周期参数
        self.MACD_SIGNAL_PERIOD = 9.0  # MACD信号线周期参数


@final
class MACD:
    """
    MACD指标类
    用于计算和存储K线的MACD技术指标数据
    MACD是缠论系统中常用的辅助判断工具，用于判断背离和能量
    """
    def __init__(self, fast_ema: float, slow_ema: float, dif: float, dea: float, fastperiod: float = 12.0, slowperiod: float = 26.0, signalperiod: float = 9.0):
        """
        初始化MACD指标对象
        
        Args:
            fast_ema: 快线指数移动平均值
            slow_ema: 慢线指数移动平均值
            dif: 快线与慢线的差值，即DIF值
            dea: DIF的指数移动平均，即DEA值
            fastperiod: 快线周期
            slowperiod: 慢线周期
            signalperiod: 信号线周期
        """
        self.fast_ema = fast_ema
        self.slow_ema = slow_ema
        self.DIF = dif
        self.DEA = dea
        self.fastperiod = fastperiod
        self.slowperiod = slowperiod
        self.signalperiod = signalperiod

    @classmethod
    def calc(cls, pre: "Bar", bar: "Bar") -> Self:
        """
        计算当前K线的MACD指标
        基于前一K线的MACD值计算当前K线的MACD
        
        Args:
            pre: 前一K线对象，包含已计算的MACD值
            bar: 当前K线对象，需要计算MACD值
            
        Returns:
            计算后的MACD对象
        """
        value = bar.close

        # 计算快线EMA
        k_fast = 2.0 / (pre.macd.fastperiod + 1.0)
        _fast_ema = value * k_fast + pre.macd.fast_ema * (1.0 - k_fast)

        # 计算慢线EMA
        k_slow = 2.0 / (pre.macd.slowperiod + 1.0)
        _slow_ema = value * k_slow + pre.macd.slow_ema * (1.0 - k_slow)

        # 计算DIF
        _dif = _fast_ema - _slow_ema

        # 计算DEA
        k_dea = 2.0 / (pre.macd.signalperiod + 1.0)
        _dea = _dif * k_dea + pre.macd.DEA * (1.0 - k_dea)

        macd = MACD(_fast_ema, _slow_ema, _dif, _dea, fastperiod=pre.macd.fastperiod, slowperiod=pre.macd.slowperiod, signalperiod=pre.macd.signalperiod)
        bar.macd = macd
        return macd

    @property
    def bar(self) -> float:
        """
        MACD柱状图值
        计算DIF与DEA之差的两倍，用于绘制柱状图
        """
        return (self.DIF - self.DEA) * 2


class Observer(metaclass=ABCMeta):
    """
    观察者抽象基类
    实现了观察者设计模式，用于通知UI等组件更新数据显示
    缠论分析中的各种对象变更都通过此类通知到前端界面
    """
    thread = None
    queue = asyncio.Queue()
    loop = asyncio.get_event_loop()

    TIME = 0.01  # 通知间隔时间，单位秒

    @abstractmethod
    def notify(self, obj: Any, cmd: Command): 
        """
        通知方法，派生类必须实现此方法
        
        Args:
            obj: 需要通知的对象
            cmd: 执行的命令
        """
        ...


class Bar:
    """
    K线类
    表示股票、期货等金融产品的基本K线数据结构
    包含时间、开高低收、成交量等基本信息
    是缠论分析的基础数据单元
    """
    __slots__ = "index", "dt", "open", "high", "low", "close", "volume", "direction", "__stamp", "macd", "shape", "_raw_start_index", "raw_end_index"

    def __init__(self, dt: datetime, o: float, high: float, low: float, c: float, v: float, i: int, stamp: str):
        """
        初始化K线对象
        
        Args:
            dt: K线的日期时间
            o: 开盘价
            high: 最高价
            low: 最低价
            c: 收盘价
            v: 成交量
            i: 索引，表示K线的顺序
            stamp: 标识符，区分普通K线和合并后的K线
        """
        self.index: int = i
        self.dt: datetime = dt
        self.open: float = o
        self.high: float = high
        self.low: float = low
        self.close: float = c
        self.volume: float = v
        if self.open > self.close:
            self.direction = Direction.Down
        else:
            self.direction = Direction.Up
        self.__stamp = stamp
        self.macd = MACD(c, c, 0.0, 0.0)

        self.shape: Optional[Shape] = None
        self._raw_start_index: int = i
        self.raw_end_index: int = i

    @property
    def stamp(self) -> str:
        """获取K线的标识符"""
        return self.__stamp

    @property
    def speck(self) -> float:
        """
        获取K线的特征价格
        根据K线形态返回对应的价格点，用于分型和笔的构建
        """
        if self.shape is Shape.G:
            return self.high
        elif self.shape is Shape.S:
            return self.high
        elif self.shape is Shape.D:
            return self.low
        elif self.shape is Shape.X:
            return self.low
        else:
            print("NewBar.speck: shape is None")
            return self.high

    def __str__(self):
        return f"{self.__class__.__name__}<{self.__stamp}>({self.dt}, {self.high}, {self.low}, index={self.index})"

    def __repr__(self):
        return f"{self.__class__.__name__}<{self.__stamp}>({self.dt}, {self.high}, {self.low}, index={self.index})"

    def __bytes__(self):
        return struct.pack(
            ">6d",
            int(self.dt.timestamp()),
            round(self.open, 8),
            round(self.high, 8),
            round(self.low, 8),
            round(self.close, 8),
            round(self.volume, 8),
        )

    def to_new_bar(self, pre) -> Self:
        """
        将原始K线转换为新K线
        新K线用于缠论分析，可能是经过处理的K线
        
        Args:
            pre: 前一个K线对象
            
        Returns:
            转换后的新K线对象
        """
        if self.stamp == "NewBar":
            return self
        return Bar.creat_new_bar_from_raw(self, pre)

    @classmethod
    def creat_new_bar_from_raw(cls, bar: Self, pre: Optional[Self] = None):
        """
        从原始K线创建新K线
        
        Args:
            bar: 原始K线
            pre: 前一个K线
            
        Returns:
            创建的新K线
        """
        return cls.creat_new_bar(bar.dt, bar.high, bar.low, bar.direction, bar.volume, bar.index, pre=pre)

    @classmethod
    def creat_new_bar(
        cls,
        dt: datetime,
        high: float,
        low: float,
        direction: Direction,
        volume: float,
        raw_index: int,
        pre: Optional[Self] = None,
    ):
        """
        创建新K线
        根据参数创建一个新的K线对象
        
        Args:
            dt: K线日期时间
            high: 最高价
            low: 最低价
            direction: 方向
            volume: 成交量
            raw_index: 原始索引
            pre: 前一个K线
            
        Returns:
            创建的新K线对象
        """
        assert high >= low
        if direction == Direction.Down:
            close = low
            _open = high
        else:
            close = high
            _open = low

        if direction is Direction.Up:
            shape = Shape.S
        else:
            shape = Shape.X

        index = 0
        nb = Bar(dt=dt, o=_open, high=high, low=low, c=close, v=volume, i=index, stamp="NewBar")
        nb._raw_start_index = raw_index
        nb.raw_end_index = raw_index
        nb.shape = shape

        if pre is not None:
            nb.index = pre.index + 1

            if double_relation(pre, nb).is_include():
                raise ChanException(f"\n    {double_relation(pre, nb)}\n    {pre},\n    {nb}")
        return nb

    @classmethod
    def creat_raw_bar(cls, dt: datetime, o: float, h: float, low: float, c: float, v: float, i: int) -> Self:
        return cls(dt, o, h, low, c, v, i, "RawBar")

    @classmethod
    def bars_save_as_dat(cls, path: str, bars: List):
        with open(path, "wb") as f:
            for bar in bars:
                f.write(bytes(bar))
        print(f"Saved {len(bars)} bars to {path}")

    @classmethod
    def from_be_bytes(cls, buf: bytes, stamp: str = "RawBar") -> Self:
        timestamp, open_, high, low, close, vol = struct.unpack(">6d", buf[: struct.calcsize(">6d")])
        return cls(
            dt=datetime.datetime.fromtimestamp(timestamp),
            o=open_,
            high=high,
            low=low,
            c=close,
            v=vol,
            i=0,
            stamp=stamp,
        )

    @classmethod
    def from_csv_file(cls, path: str, stamp: str = "RawBar") -> List[Self]:
        raws: List = []
        with open(path, "r") as f:
            stamps = f.readline().split(",")
            ts = stamps.index("timestamp")
            o = stamps.index("open")
            h = stamps.index("high")
            low = stamps.index("low")
            c = stamps.index("close")
            v = stamps.index("volume")
            i = 0
            for line in f.readlines():
                info = line.split(",")
                rb = Bar(datetime.datetime.strptime(info[ts], "%Y-%m-%d %H:%M:%S"), float(info[o]), float(info[h]), float(info[low]), float(info[c]), float(info[v]), i, stamp)
                raws.append(rb)
                i += 1

        return raws

    @classmethod
    def generate(cls, bar: "Bar", direction: Direction, seconds: int, half: bool = False) -> Self:
        offset = datetime.timedelta(seconds=seconds)
        dt: datetime = bar.dt + offset
        volume: float = 998
        raw_index: int = bar._raw_start_index + 1
        high: float = 0
        low: float = 0
        d = bar.high - bar.low
        match direction:
            case Direction.Up:
                i = d * 0.5 if half else randint(int(d * 0.1279), int(d * 0.883))
                low: float = bar.low + i
                high: float = bar.high + i
            case Direction.Down:
                i = d * 0.5 if half else randint(int(d * 0.1279), int(d * 0.883))
                low: float = bar.low - i
                high: float = bar.high - i
            case Direction.JumpUp:
                i = d * 1.5 if half else randint(int(d * 1.1279), int(d * 1.883))
                low: float = bar.low + i
                high: float = bar.high + i
            case Direction.JumpDown:
                i = d * 1.5 if half else randint(int(d * 1.1279), int(d * 1.883))
                low: float = bar.low - i
                high: float = bar.high - i
            case Direction.NextUp:
                i = bar.high - bar.low
                high: float = bar.high + i
                low: float = bar.high
            case Direction.NextDown:
                i = bar.high - bar.low
                high: float = bar.low
                low: float = bar.low - i

        nb = Bar.creat_new_bar(dt, high, low, Direction.Up if direction.is_up() else Direction.Down, volume, raw_index, bar)
        nb.index = bar.index + 1
        assert double_relation(bar, nb) is direction, (direction, double_relation(bar, nb))
        return nb

    @classmethod
    def merger(cls, pre: Optional[Self], bar: Self, next_raw_bar: Self) -> Optional[Self]:
        if not double_relation(bar, next_raw_bar).is_include():
            nb = next_raw_bar.to_new_bar(bar)
            nb.index = bar.index + 1
            return nb

        if next_raw_bar.index - 1 != bar.raw_end_index:
            raise ChanException(f"NewBar.merger: 不可追加不连续元素 bar.raw_end_index: {bar.raw_end_index}, next_raw_bar.index: {next_raw_bar.index}.")

        direction = Direction.Up
        if pre is not None:
            if double_relation(pre, bar).is_down():
                direction = Direction.Down

        func = max
        if direction is Direction.Down:
            func = min
        bar.high = func(bar.high, next_raw_bar.high)
        bar.low = func(bar.low, next_raw_bar.low)
        bar.open = bar.high if bar.direction is Direction.Down else bar.low
        bar.close = bar.low if bar.direction is Direction.Down else bar.high
        bar.raw_end_index = next_raw_bar.index

        if pre is not None:
            bar.index = pre.index + 1
        return None


class FenXing:
    """
    分型类
    缠论分析中的关键概念，代表K线的局部转折点
    包含顶分型、底分型、上升分型和下降分型等形态
    由三根K线构成，需满足特定的走势关系
    """
    __slots__ = "index", "left", "mid", "right"

    def __init__(self, left: Bar, mid: Bar, right: Bar, index: int = 0):
        """
        初始化分型对象
        
        Args:
            left: 左侧K线
            mid: 中间K线，代表分型的核心点
            right: 右侧K线
            index: 分型索引
        """
        self.left = left
        self.mid = mid
        self.right = right
        self.index = index

    @property
    def dt(self) -> datetime.datetime:
        """获取分型的日期时间，使用中间K线的时间"""
        return self.mid.dt

    @property
    def shape(self) -> Shape:
        """获取分型的形态，由中间K线的形态决定"""
        return self.mid.shape

    @property
    def speck(self) -> float:
        """获取分型的特征价格，由中间K线的特征价格决定"""
        return self.mid.speck

    @property
    def high(self) -> float:
        """获取分型的最高价，取左侧和中间K线的最高价中的最大值"""
        return max(self.left.high, self.mid.high)

    @property
    def low(self) -> float:
        """获取分型的最低价，取左侧和中间K线的最低价中的最小值"""
        return min(self.left.low, self.mid.low)

    def __str__(self):
        """返回分型的字符串表示"""
        return f"FenXing({self.shape}, {self.speck}, {self.dt})"

    def __repr__(self):
        """返回分型的字符串表示，用于调试和打印"""
        return f"FenXing({self.shape}, {self.speck}, {self.dt})"

    def get_shape(self) -> Shape:
        """
        获取分型的形态
        通过三K线关系判断分型类型
        
        Returns:
            分型形态
        """
        shape, (_, _), _ = triple_relation(self.left, self.mid, self.right)
        return shape

    def get_relations(self) -> (Direction, Direction): # type: ignore
        """
        获取分型内部的关系
        返回左中和中右的关系
        
        Returns:
            (左中关系, 中右关系)的元组
        """
        _, (lm, mr), _ = triple_relation(self.left, self.mid, self.right)
        return lm, mr

    @staticmethod
    def get_fenxing(bars: List[Bar], mid: Bar) -> "FenXing":
        """
        从K线列表中获取特定中间K线的分型
        
        Args:
            bars: K线列表
            mid: 中间K线
            
        Returns:
            构建的分型对象
        """
        index = bars.index(mid)
        return FenXing(bars[index - 1], mid, bars[index + 1])

    @staticmethod
    def append(fxs, fx):
        """
        添加分型到分型列表
        
        Args:
            fxs: 分型列表
            fx: 需要添加的分型
        """
        if fxs and fxs[-1].shape is fx.shape:
            raise ChanException("分型相同无法添加", fxs[-1], fx)
        i = 0
        if fxs:
            i = fxs[-1].index + 1
        fx.index = i
        fxs.append(fx)

    @staticmethod
    def pop(fxs, fx):
        """
        从分型列表中移除指定分型
        
        Args:
            fxs: 分型列表
            fx: 需要移除的分型
            
        Returns:
            移除的分型
        """
        if fxs and fxs[-1] is not fx:
            raise ChanException("分型相同无法删除", fxs[-1], fx)
        return fxs.pop()


class Line(metaclass=ABCMeta):
    """
    线段抽象基类
    缠论分析中的基础线对象，用作笔和线段的父类
    代表从一个分型到另一个分型的连线，是构成笔和线段的基础
    """
    __slots__ = "pre", "next", "index", "__start", "__end", "__stamp", "__elements"

    def __init__(self, start: FenXing, end: FenXing, index: int, elements: List | Set, stamp: str = "Line"):
        """
        初始化线对象
        
        Args:
            start: 起始分型
            end: 结束分型
            index: 索引
            elements: 组成该线的元素列表
            stamp: 标识符，用于区分不同类型的线
        """
        self.index: int = index
        self.pre: Optional[Self] = None  # 前一条线
        self.next: Optional[Self] = None  # 后一条线
        self.__start = start
        self.__end = end
        self.__stamp = stamp
        self.__elements = elements

    def __len__(self):
        """返回线包含的元素数量"""
        return len(self.elements)

    def __iter__(self):
        """迭代线中的元素"""
        return iter(self.elements)

    def __hash__(self):
        """计算线的哈希值，用于字典和集合"""
        return hash(f"{self.stamp} {self.start.mid}")

    def __eq__(self, other):
        """
        比较两条线是否相等
        
        Args:
            other: 另一个对象
            
        Returns:
            如果类型、标识符、起始点、终点、元素和索引都相同，则认为相等
        """
        return type(other) is self and self.stamp == other.stamp and self.start == other.start and self.end == other.end and self.elements == other.elements and self.index == other.index

    @property
    @final
    def stamp(self) -> str:
        """获取线的标识符"""
        return self.__stamp

    @property
    @final
    def elements(self) -> List[Self]:
        """获取线包含的元素列表"""
        return self.__elements

    @elements.setter
    def elements(self, elements: List[Self]):
        """设置线包含的元素列表"""
        self.__elements = elements

    @property
    def start(self) -> FenXing:
        """获取线的起始分型"""
        return self.__start

    @property
    def end(self) -> FenXing:
        """获取线的结束分型"""
        return self.__end

    @end.setter
    @final
    def end(self, end: FenXing):
        """设置线的结束分型"""
        self.__end = end

    @property
    @final
    def direction(self) -> Direction:
        """
        获取线的方向
        通过起始和结束分型的类型判断方向
        
        Returns:
            线的方向，上升或下降
        """
        if self.start.shape is Shape.G and self.end.shape is Shape.D:
            return Direction.Down
        elif self.start.shape is Shape.D and self.end.shape is Shape.G:
            return Direction.Up
        else:
            raise ChanException(f"{self.stamp}.direction: {self.start.shape}, {self.end.shape}, {self.stamp}")

    @property
    def high(self) -> float:
        """
        获取线的最高点
        根据线的方向不同，可能是起点或终点
        
        Returns:
            线的最高价格
        """
        if self.direction == Direction.Down:
            return self.start.speck
        else:
            return self.end.speck

    @property
    def low(self) -> float:
        """
        获取线的最低点
        根据线的方向不同，可能是起点或终点
        
        Returns:
            线的最低价格
        """
        if self.direction == Direction.Up:
            return self.start.speck
        else:
            return self.end.speck

    @property
    def open(self) -> float:
        """
        获取线的开盘价
        根据线的方向不同，可能是起点或终点
        
        Returns:
            线的开盘价格
        """
        if self.direction == Direction.Down:
            return self.high
        else:
            return self.low

    @property
    def close(self) -> float:
        """
        获取线的收盘价
        根据线的方向不同，可能是起点或终点
        
        Returns:
            线的收盘价格
        """
        if self.direction == Direction.Up:
            return self.high
        else:
            return self.low

    def calc_angle(self) -> float:
        """
        计算线段的角度
        使用数学atan2函数计算线段与水平轴的夹角
        
        Returns:
            线段角度，单位为度
        """
        # 计算线段的角度
        dx = self.end.mid.index - self.start.mid.index  # 横轴距离（索引差值）
        dy = self.end.speck - self.start.speck  # 纵轴距离（价格差值）

        if dx == 0:
            return 90.0 if dy > 0 else -90.0

        angle = math.degrees(math.atan2(dy, dx))
        return angle

    def calc_speed(self) -> float:
        """
        计算线段的速度
        即价格变化与时间变化的比值
        
        Returns:
            线段速度，表示单位时间内的价格变化率
        """
        # 计算线段的速度
        dx = self.end.mid.index - self.start.mid.index  # 时间差（索引差）
        dy = self.end.speck - self.start.speck  # 价格差
        return dy / dx

    def calc_measure(self) -> float:
        """
        计算线段测度
        使用欧几里得距离计算线段的长度
        
        Returns:
            线段的欧几里得长度（测度）
        """
        # 计算线段测度
        dx = self.end.mid.index - self.start.mid.index  # 横轴距离（索引差值）
        dy = abs(self.end.speck - self.start.speck)  # 纵轴距离（价格差值）的绝对值
        return math.sqrt(dx * dx + dy * dy)  # 返回线段的欧几里得长度作为测度

    def calc_amplitude(self) -> float:
        """
        计算线段振幅比例
        即价格变化占起始价格的比例
        
        Returns:
            线段振幅比例，表示价格变化的相对比例
        """
        # 计算线段振幅比例
        amplitude = self.end.speck - self.start.speck
        return amplitude / self.start.speck if self.start.speck != 0 else 0

    def calc_macd(self) -> Dict[str, float]:
        """
        计算线段的MACD指标汇总
        统计组成线段的各元素的MACD指标值，分别累计向上和向下的部分
        
        Returns:
            包含上升力量、下降力量和总量的字典
        """
        result = {"up": 0.0, "down": 0.0, "sum": 0.0}
        for element in self.elements:
            if hasattr(element, "macd"):
                macd = element.macd
                key = "up" if macd.bar > 0 else "down"
                result[key] = result[key] + macd.bar

            else:
                macd = element.calc_macd()
                result["up"] = result["up"] + macd["up"]
                result["down"] = result["down"] + macd["down"]

        result["sum"] = abs(result["up"]) + abs(result["down"])
        return result

    def is_previous(self, line: "Line") -> bool:
        """
        检查给定的线是否是当前线的前一条线
        通过比较线的结束点和起始点判断
        
        Args:
            line: 要检查的线
            
        Returns:
            如果给定的线的结束点是当前线的起始点，则返回True
        """
        return line.end is self.start

    def is_next(self, line: "Line") -> bool:
        """
        检查给定的线是否是当前线的后一条线
        通过比较线的起始点和结束点判断
        
        Args:
            line: 要检查的线
            
        Returns:
            如果当前线的结束点是给定的线的起始点，则返回True
        """
        return self.end is line.start

    def get_line(self) -> "Line":
        """
        获取当前线的副本
        创建一个与当前线具有相同起点、终点、索引和元素的新线对象
        
        Returns:
            新创建的Line对象
        """
        return Line(self.start, self.end, self.index, self.elements, self.stamp)

    def get_bars(self, bars: list) -> List[Bar]:
        """
        获取线段覆盖的K线列表
        从起始K线到结束K线之间的所有K线
        
        Args:
            bars: 完整的K线列表
            
        Returns:
            线段覆盖的K线子列表
        """
        return bars[bars.index(self.start.mid) : bars.index(self.end.mid) + 1]

    @classmethod
    def append(cls, lines: List["Line"], line: "Line"):
        """
        添加一条线到线列表中
        并设置前后关系和索引
        
        Args:
            lines: 线列表
            line: 要添加的线
            
        Raises:
            ChanException: 如果新线与列表中最后一条线不连续
        """
        if lines and not lines[-1].is_next(line):
            raise ChanException("Line.append 不连续", lines[-1], line)

        if lines:
            line.index = lines[-1].index + 1
            line.pre = lines[-1]
            if len(lines) > 1:
                lines[-2].next = lines[-1]

        lines.append(line)

    @classmethod
    def pop(cls, lines: List["Line"], line: "Line") -> Optional["Line"]:
        """
        从线列表中移除指定的线
        
        Args:
            lines: 线列表
            line: 要移除的线
            
        Returns:
            被移除的线对象，如果列表为空则返回None
            
        Raises:
            ChanException: 如果要移除的线不在列表的末尾
        """
        if not lines:
            return

        if lines[-1] is line:
            drop = lines.pop()
            return drop
        raise ChanException("Line.pop 弹出数据不在列表中")

    @classmethod
    @final
    def create(cls, obj: List | "Line", stamp: str) -> "Line":
        """
        创建一条新的线
        可以基于一条已有的线或多条线创建新线
        
        Args:
            obj: 一条线或线列表
            stamp: 新线的标识符
            
        Returns:
            创建的新Line对象
        """
        if type(obj) is list:
            lines: List["Line"] = obj[:]
            return Line(lines[0].start, lines[-1].end, 0, lines, stamp)
        line: "Line" = obj
        return Line(line.start, line.end, 0, [line], stamp)


class Interval:
    """
    区间类
    表示由多个线段组成的价格区间
    用于中枢分析的基本构建块
    """
    __slots__ = "index", "elements", "__high", "__low"

    def __init__(self, elements: List, high: float, low: float):
        """
        初始化区间对象
        
        Args:
            elements: 组成区间的元素列表
            high: 区间的高点
            low: 区间的低点
        """
        self.elements = elements
        self.__high = high
        self.__low = low
        self.index = 0

    def __str__(self):
        """返回区间的字符串表示"""
        return f"Interval({self.index}, {len(self)}, {self.__high}, {self.__low})"

    def __len__(self):
        """返回区间包含的元素数量"""
        return len(self.elements)

    def __iter__(self):
        """迭代区间中的元素"""
        return iter(self.elements)

    @property
    def high(self) -> int | float:
        """获取区间的高点"""
        return self.__high

    @property
    def low(self) -> int | float:
        """获取区间的低点"""
        return self.__low

    @property
    def start(self) -> FenXing:
        """获取区间的起始分型"""
        return self.elements[0].start

    @property
    def end(self) -> FenXing:
        """获取区间的结束分型"""
        return self.elements[-1].end

    def is_next(self, element: Any) -> bool:
        """
        检查给定的元素是否是区间的下一个元素
        
        Args:
            element: 要检查的元素
            
        Returns:
            如果元素类型匹配且索引连续，则返回True
        """
        if type(element) is not type(self.elements[-1]):
            return False

        if element.index - 1 != self.elements[-1].index:
            return False

        return True

    def extend(self, obj) -> tuple["Interval", bool]:
        """
        扩展区间，添加新的元素
        
        Args:
            obj: 要添加的元素
            
        Returns:
            包含自身和是否成功添加的元组
        """
        relation = double_relation(self, obj)
        flag = False
        if not any((relation.is_next(), relation.is_jump())) and self.is_next(obj):
            self.elements.append(obj)
            flag = True
        return self, flag

    def check(self) -> Optional[bool]:
        """
        检查区间的有效性
        验证区间内元素之间的关系
        
        Returns:
            如果区间有效，返回True；如果无效，返回False；如果需要截断，返回None
        """
        tmp = Interval.new(self.elements)
        if tmp:
            for i in range(3, len(self.elements) - 1):
                hl = self.elements[i]
                if double_relation(self, hl).is_jump():
                    if i != len(self.elements) - 1:
                        self.elements = self.elements[:i]
                    return None
            return True
        return False

    @classmethod
    def new(cls, elements) -> Optional["Interval"]:
        """
        创建新的区间
        从元素列表中创建一个新的区间对象
        
        Args:
            elements: 构成区间的元素列表
            
        Returns:
            新创建的Interval对象，如果不能构成有效区间则返回None
        """
        if len(elements) < 3:
            return

        lr = double_relation(elements[0], elements[2])
        if lr.is_jump():
            return

        lm = double_relation(elements[0], elements[1])
        if lm.is_jump():
            return

        mr = double_relation(elements[1], elements[2])
        if mr.is_jump():
            return

        high = min([hl.high for hl in elements[:3]])
        low = max([hl.low for hl in elements[:3]])
        return cls(elements, high, low)

    @classmethod
    def analyzer(cls, hls: List, intervals: List["Interval"], observer: Observer, style: str = ""):
        """
        分析区间
        对元素列表进行分析，找出所有可能的区间
        
        Args:
            hls: 待分析的元素列表
            intervals: 已发现的区间列表
            observer: 观察者对象，用于通知UI更新
            style: 分析风格
            
        Returns:
            分析后的区间列表
        """
        if style != "":
            intervals = []
            for i in range(1, len(hls) - 1):
                new = cls.new([hls[i - 1], hls[i], hls[i + 1]])
                if new is not None:
                    intervals.append(new)
            return intervals

        if not intervals:
            for i in range(1, len(hls) - 1):
                new = cls.new([hls[i - 1], hls[i], hls[i + 1]])
                if new is not None:
                    intervals.append(new)
                    observer.notify(new, Command.Append("nb"))
                    return cls.analyzer(hls, intervals, observer)

        else:
            last = intervals[-1]
            flag: Optional[bool] = last.check()
            if flag is None:
                index = hls.index(last.elements[2]) + 1
            elif flag is True:
                index = hls.index(last.elements[-1]) + 1
            else:
                intervals.pop()
                observer.notify(last, Command.Remove("nb"))
                return cls.analyzer(hls, intervals, observer)

            observer.notify(last, Command.Modify("nb"))

            while index == -1:
                try:
                    index = hls.index(last.elements[-1]) + 1
                    break
                except ValueError:
                    if len(last) > 3:
                        last.elements.pop()
                    else:
                        drop = intervals.pop()
                        observer.notify(drop, Command.Remove("nb"))
                        return cls.analyzer(hls, intervals, observer)

            elements = []
            for hl in hls[index:]:
                if double_relation(last, hl).is_jump():
                    if not elements:
                        elements.append(last.elements[-1])
                    elements.append(hl)
                else:
                    if not elements:
                        if hl not in last.elements:
                            last.elements.append(hl)
                        observer.notify(last, Command.Modify("nb"))
                    else:
                        elements.append(hl)

                if len(elements) >= 3:
                    new = cls.new(elements[:])
                    if new is None:
                        elements.pop(0)
                    else:
                        intervals.append(new)
                        new.index = last.index + 1
                        observer.notify(new, Command.Append("nb"))
                        last = new
                        elements.clear()


class Lines:
    """
    线列表类
    管理一组线（Line）对象的容器
    提供添加、删除和索引等基础操作
    """
    def __init__(self, elements: List[Line]):
        """
        初始化线列表对象
        
        Args:
            elements: 线对象列表
        """
        self.__elements = elements

    def __len__(self):
        """返回线列表的长度"""
        return len(self.__elements)

    def __iter__(self):
        """迭代线列表中的元素"""
        return iter(self.__elements)

    def __next__(self):
        """获取迭代的下一个元素"""
        return next(self)

    def __getitem__(self, index):
        """通过索引获取线对象"""
        return self.__elements[index]

    def __setitem__(self, index, value):
        """通过索引设置线对象的值"""
        self.__elements[index] = value

    def __delitem__(self, index):
        """通过索引删除线对象"""
        del self.__elements[index]

    def append(self, element: Line):
        """
        添加线对象到列表末尾
        并设置相邻线对象之间的前后关系
        
        Args:
            element: 要添加的线对象
        """
        length = len(self.__elements)
        if length > 0:
            last = self.__elements[-1]
            assert last.end is element.start
            if last.index + 1 != element.index:
                element.index = last.index + 1
                element.pre = last
                if length > 1:
                    pre = self.__elements[-2]
                    pre.next = last

        self.__elements.append(element)

    def pop(self, index=-1):
        """
        移除并返回指定索引的线对象
        
        Args:
            index: 要移除的线对象的索引，默认为最后一个
            
        Returns:
            被移除的线对象
        """
        return self.__elements.pop(index)

    def index(self, element: Line):
        """
        查找线对象在列表中的索引
        
        Args:
            element: 要查找的线对象
            
        Returns:
            线对象在列表中的索引
        """
        return self.__elements.index(element)

    def clear(self):
        """清空线列表"""
        self.__elements.clear()

    def reset_line_index(self):
        """
        重置所有线对象的索引
        使索引值与线对象在列表中的位置一致
        """
        for index, element in enumerate(self.__elements):
            element.index = index
        print("Lines reset line index done!", len(self.__elements))

    def reset_line_next_and_pre(self):
        """
        重置所有线对象之间的前后关系
        确保相邻线对象之间的pre和next指针正确连接
        """
        for i in range(1, len(self.__elements)):
            if hasattr(self.__elements[i - 1], "next"):
                self.__elements[i - 1].next = self.__elements[i]
            if hasattr(self.__elements[i - 1], "pre"):
                self.__elements[i].pre = self.__elements[i - 1]


@final
class FeatureSequence(Line):
    """
    特征序列类
    继承自Line，表示具有相同方向特征的一组线段
    用于构建缠论中的高级别走势结构
    """
    def __init__(self, elements: Set[Line]):
        """
        初始化特征序列对象
        
        Args:
            elements: 具有相同方向特征的线段集合
        """
        start: FenXing = tuple(elements)[0].start
        end: FenXing = tuple(elements)[0].end
        super().__init__(start, end, 0, elements, f"FeatureSequence<{tuple(elements)[0].stamp if len(elements) > 0 else None}>")

    def __str__(self):
        """返回特征序列的字符串表示"""
        return f"特征序列({self.direction}, {self.start.dt}, {self.end.dt}, {len(self.elements)}, {self.stamp})"

    def __repr__(self):
        """返回特征序列的字符串表示，用于调试和打印"""
        return f"特征序列({self.direction}, {self.start.dt}, {self.end.dt}, {len(self.elements)}, {self.stamp})"

    @property
    def start(self) -> FenXing:
        """
        获取特征序列的起始分型
        根据方向不同，选择集合中所有线段起始点中的最低点或最高点
        
        Returns:
            特征序列的起始分型
        """
        direction = tuple(self.elements)[0].direction
        if direction is Direction.Down:  # Down特征序列 为 Up线段, 取高高
            func = max
        else:
            func = min
        fx = func([line.start for line in self.elements], key=lambda o: o.speck)
        assert fx.shape in (Shape.G, Shape.D)
        return fx

    @property
    def end(self) -> FenXing:
        """
        获取特征序列的结束分型
        根据方向不同，选择集合中所有线段结束点中的最低点或最高点
        
        Returns:
            特征序列的结束分型
        """
        direction = tuple(self.elements)[0].direction
        if direction is Direction.Down:  # Down特征序列 为 Up线段, 取高高
            func = max
        else:
            func = min
        fx = func([line.end for line in self.elements], key=lambda o: o.speck)
        assert fx.shape in (Shape.G, Shape.D)
        return fx

    @property
    def high(self) -> float:
        """
        获取特征序列的最高点
        从起始点和结束点中取最高值
        
        Returns:
            特征序列的最高价格
        """
        return max([self.end, self.start], key=lambda fx: fx.speck).speck

    @property
    def low(self) -> float:
        """
        获取特征序列的最低点
        从起始点和结束点中取最低值
        
        Returns:
            特征序列的最低价格
        """
        return min([self.end, self.start], key=lambda fx: fx.speck).speck

    def add(self, line: Line):
        """
        添加线段到特征序列
        要求添加的线段与特征序列的方向一致
        
        Args:
            line: 要添加的线段
            
        Raises:
            ChanException: 如果线段方向与特征序列方向不匹配
        """
        direction = tuple(self.elements)[0].direction
        if line.direction != direction:
            raise ChanException("方向不匹配", direction, line, self)
        self.elements.add(line)

    def remove(self, line: Line):
        """
        从特征序列中移除线段
        
        Args:
            line: 要移除的线段
            
        Raises:
            ChanException: 如果线段方向与特征序列方向不匹配
            Exception: 如果移除操作失败
        """
        direction = tuple(self.elements)[0].direction
        if line.direction != direction:
            raise ChanException("方向不匹配", direction, line, self)

        try:
            self.elements.remove(line)
        except Exception as e:
            print(self)
            raise e

    @classmethod
    def analyzer(cls, lines: List[Line], direction: Direction, combines: Tuple[Direction] = (Direction.Left,)) -> Tuple[Optional["FeatureSequence"], Optional["FeatureSequence"], Optional["FeatureSequence"]]:
        """
        分析特征序列
        从线段列表中分析提取特征序列
        
        Args:
            lines: 线段列表
            direction: 特征序列的方向
            combines: 可以组合的关系类型，默认为顺序包含关系
            
        Returns:
            包含三个特征序列的元组，分别代表左、中、右特征序列
        """
        if combines is None:
            combines = (Direction.Left,)
        features: List[FeatureSequence] = []
        for obj in lines:
            if obj.direction is direction:
                if len(features) >= 3:
                    left, mid, right = features[-3], features[-2], features[-1]
                    shape, (_, _), _ = triple_relation(left, mid, right, use_right=True, ignore=True)
                    if (direction is Direction.Up and shape is Shape.G and obj.high > mid.high) or (direction is Direction.Down and shape is Shape.D and obj.low < mid.low):
                        start = min(mid.elements, key=lambda o: o.index)
                        end = max(right.elements, key=lambda o: o.index)
                        elements = lines[lines.index(start) : lines.index(end) + 1]
                        fake = Line(start.start, end.end, 0, elements, f"Fake-{start.stamp}")
                        feature = FeatureSequence({fake})
                        features.pop()
                        features[-1] = feature

                continue
            if features:
                last = features[-1]

                if double_relation(last, obj) in combines:
                    last.add(obj)
                else:
                    features.append(FeatureSequence({obj}))
            else:
                features.append(FeatureSequence({obj}))

        length = len(features)
        if length == 1:
            return features[0], None, None
        if length == 2:
            return features[0], features[1], None
        if length >= 3:
            relation = double_relation(features[-2], features[-1])
            if direction is Direction.Up:
                if relation.is_down():
                    return features[-3], features[-2], features[-1]
                else:
                    return features[-2], features[-1], None
            else:
                if relation.is_up():
                    return features[-3], features[-2], features[-1]
                else:
                    return features[-2], features[-1], None

        return None, None, None


class ZhongShuState(Enum):
    """
    中枢状态枚举类
    表示缠论中枢在分析过程中的不同状态
    用于跟踪中枢的形成和演变过程
    """

    FORMING = "形成中"  # 初始形成的3段
    EXTENDING = "延伸中"  # 在原有区间内延伸
    EXPANDING = "扩张中"  # 与其他中枢发生扩展
    ENDED = "已完成"  # 中枢结束


class ZhongShuType(Enum):
    """
    中枢类型枚举类
    表示缠论中枢根据形成方式的不同类型
    用于区分不同演化阶段的中枢
    """

    ORIGINAL = "原始中枢"  # 最初形成的中枢
    EXTENDED = "延伸中枢"  # 延伸后的中枢
    EXPANDED = "扩张中枢"  # 扩展后的中枢(新的高级别中枢)


class ZhongShu:
    """
    中枢类
    缠论分析中的核心概念，表示价格波动中的震荡区间
    由至少三段方向相反的线段组成，形成一个价格区间
    """
    __slots__ = "index", "elements", "third", "__stamp", "__direction"

    def __init__(self, direction: Direction, lines: List[Line]):
        """
        初始化中枢对象
        
        Args:
            direction: 中枢的方向
            lines: 构成中枢的线段列表，通常至少包含三段
        """
        self.index: int = 0
        self.__direction = direction
        self.elements: List[Line] = list(lines)
        self.third: Optional[Line] = None
        self.__stamp = lines[0].stamp

    def __str__(self):
        """返回中枢的字符串表示"""
        return f"{self.stamp}中枢({self.index}, {self.direction}, {self.third is not None}, {self.zg}, {self.zd}, elements size={len(self.elements)})"

    def __repr__(self):
        """返回中枢的字符串表示，用于调试和打印"""
        return f"{self.stamp}中枢({self.index}, {self.direction}, {self.third is not None}, {self.zg}, {self.zd}, elements size={len(self.elements)})"

    @property
    def stamp(self) -> str:
        """获取中枢的标识符"""
        return f"ZhongShu<{self.__stamp}>"

    @property
    def left(self) -> Optional[Line]:
        """获取中枢的第一段线段"""
        return self.elements[0] if self.elements else None

    @property
    def mid(self) -> Optional[Line]:
        """获取中枢的第二段线段"""
        return self.elements[1] if len(self.elements) > 1 else None

    @property
    def right(self) -> Optional[Line]:
        """获取中枢的第三段线段"""
        return self.elements[2] if len(self.elements) > 2 else None

    @property
    def direction(self) -> Direction:
        """
        获取中枢的方向
        由构成中枢的线段方向决定
        
        Returns:
            中枢的方向
        """
        return self.__direction
        # return Direction.Down if self.start.shape is Shape.D else Direction.Up

    @property
    def zg(self) -> float:
        """
        获取中枢上沿价格
        取前三段线段高点的最低值
        
        Returns:
            中枢上沿价格
        """
        return min(self.elements[:3], key=lambda o: o.high).high

    @property
    def zd(self) -> float:
        """
        获取中枢下沿价格
        取前三段线段低点的最高值
        
        Returns:
            中枢下沿价格
        """
        return max(self.elements[:3], key=lambda o: o.low).low

    @property
    def g(self) -> float:
        """
        获取中枢区间内所有线段的最低高点
        
        Returns:
            中枢区间内所有线段高点的最低值
        """
        return min(self.elements, key=lambda o: o.high).high

    @property
    def d(self) -> float:
        """
        获取中枢区间内所有线段的最高低点
        
        Returns:
            中枢区间内所有线段低点的最高值
        """
        return max(self.elements, key=lambda o: o.low).low

    @property
    def gg(self) -> float:
        """
        获取中枢区间内所有线段的最高点
        
        Returns:
            中枢区间内所有线段高点的最高值
        """
        return max(self.elements, key=lambda o: o.high).high

    @property
    def dd(self) -> float:
        """
        获取中枢区间内所有线段的最低点
        
        Returns:
            中枢区间内所有线段低点的最低值
        """
        return min(self.elements, key=lambda o: o.low).low

    @property
    def high(self) -> float:
        """获取中枢的上沿价格，同zg"""
        return self.zg

    @property
    def low(self) -> float:
        """获取中枢的下沿价格，同zd"""
        return self.zd

    @property
    def start(self) -> FenXing:
        """获取中枢的起始分型"""
        return self.elements[0].start

    @property
    def end(self) -> FenXing:
        """获取中枢的结束分型"""
        return self.elements[-1].end

    @property
    def last(self) -> Line:
        """获取中枢的最后一段线段"""
        return self.elements[-1]

    def update(self, lines: List[Line]) -> bool:
        """
        更新中枢，添加新的线段
        
        Args:
            lines: 线段列表
            
        Returns:
            是否成功更新
        """
        i = self.elements[-1].index

        while 1:
            try:
                lines.index(self.elements[-1])
                break
            except ValueError:
                _ = Line.pop(self.elements, self.elements[-1])

        fixed = False
        for line in lines:
            if self.elements[-1].is_next(line):
                self.elements.append(line)
                fixed = True
                if line.index == i:
                    break
        return fixed

    def check(self) -> bool:
        """
        检查中枢的有效性
        验证中枢初始三段线段之间的关系是否符合中枢定义
        
        Returns:
            如果中枢有效，返回True
        """
        return double_relation(self.left, self.right) in (
            Direction.Down,
            Direction.Up,
            Direction.Left,
            Direction.Right,
        )

    def get_elements(self) -> List[Line]:
        """
        获取中枢的所有元素
        包括构成中枢的线段和可能的第三段线段
        
        Returns:
            中枢的所有线段列表
        """
        elements: List[Line] = self.elements[:]
        if self.third is not None:
            elements.append(self.third)
        return elements

    @classmethod
    def append(cls, zss: List["ZhongShu"], zs: "ZhongShu", observer: Observer):
        """
        添加中枢到中枢列表
        并设置索引和通知观察者
        
        Args:
            zss: 中枢列表
            zs: 要添加的中枢
            observer: 观察者对象，用于通知UI更新
            
        Raises:
            ChanException: 如果添加操作导致索引不一致
        """
        if zss:
            zs.index = zss[-1].index + 1
            if zss[-1].get_elements()[-1].index > zs.get_elements()[-1].index:
                raise ChanException()
        zss.append(zs)
        zsdp(f"ZhongShu.append: {zs}")
        observer and observer.notify(zs, Command.Append(zs.stamp + "_zs"))

    @classmethod
    def pop(cls, zss: List["ZhongShu"], zs: "ZhongShu", observer: Observer) -> Optional["ZhongShu"]:
        """
        从中枢列表中移除指定的中枢
        
        Args:
            zss: 中枢列表
            zs: 要移除的中枢
            observer: 观察者对象，用于通知UI更新
            
        Returns:
            被移除的中枢，如果列表为空则返回None
        """
        if not zss:
            return
        if zss[-1] is zs:
            zsdp(f"ZhongShu.pop: {zs}")
            observer and observer.notify(zs, Command.Remove(zs.stamp + "_zs"))
            return zss.pop()

    @classmethod
    def new(cls, elements: List[Line]) -> Optional["ZhongShu"]:
        """
        创建新的中枢
        从线段列表中创建一个新的中枢对象
        
        Args:
            elements: 构成中枢的线段列表
            
        Returns:
            新创建的ZhongShu对象，如果不能构成有效中枢则返回None
        """
        if Interval.new(elements) is not None:
            return ZhongShu(elements[1].direction, elements)

    @classmethod
    def analyzer(cls, lines: List[Line], zss: List["ZhongShu"], observer: Optional[Observer]):
        """
        分析中枢
        从线段列表中分析提取中枢
        
        Args:
            lines: 线段列表
            zss: 已发现的中枢列表
            observer: 观察者对象，用于通知UI更新
        """
        if not lines:
            return

        if not zss:
            for i in range(1, len(lines) - 1):
                left, mid, right = lines[i - 1], lines[i], lines[i + 1]
                new = cls.new([left, mid, right])
                if new is not None:
                    if left.index == 0:
                        continue  # 方便计算走势

                    cls.append(zss, new, observer)
                    return cls.analyzer(lines, zss, observer)

        else:
            last = zss[-1]
            tmp = Interval.new(last.elements)
            if tmp is None:
                cls.pop(zss, last, observer)
                return cls.analyzer(lines, zss, observer)
            else:
                if last.high == tmp.high and last.low == tmp.low:
                    ...
                else:
                    cls.pop(zss, last, observer)
                    return cls.analyzer(lines, zss, observer)

            if last.third is not None:
                if not double_relation(last, last.third).is_jump():
                    last.elements.append(last.third)
                    last.third = None
                    observer and observer.notify(last, Command.Modify(last.stamp))

            while 1:
                try:
                    index = lines.index(last.elements[-1]) + 1
                    break
                except ValueError:
                    if len(last.elements) > 3:
                        last.elements.pop()
                        observer and observer.notify(last, Command.Modify(last.stamp))
                    else:
                        cls.pop(zss, last, observer)
                        return cls.analyzer(lines, zss, observer)

            elements = []
            for hl in lines[index:]:
                if double_relation(last, hl).is_jump():
                    elements.append(hl)
                    if last.elements[-1].is_next(hl):
                        last.third = hl
                else:
                    if not elements:
                        last.elements.append(hl)
                        observer and observer.notify(last, Command.Modify(last.stamp))
                    else:
                        elements.append(hl)

                if len(elements) >= 3:
                    new = cls.new(elements[:])
                    if new is None:
                        elements.pop(0)
                    else:
                        relation = double_relation(last, new)
                        if relation.is_up():
                            if elements[0].direction == Direction.Up:
                                elements.pop(0)
                                continue
                        elif relation.is_down():
                            if elements[0].direction == Direction.Down:
                                elements.pop(0)
                                continue
                        else:
                            print(colored(f"{relation}", "red"))

                        cls.append(zss, new, observer)
                        last = new
                        elements = []


@final
class Bi(Line):
    """
    笔类
    缠论分析中的基本构成单位，由两个分型之间的连线组成
    表示价格的一个完整起伏，必须满足一定的长度和形态要求
    是构建线段的基础
    """
    __slots__ = "fake", "config"

    def __init__(
        self,
        pre: Optional["Self"],
        start: FenXing,
        end: FenXing,
        elements: List[Bar],
        fake: bool,
        config: ChanConfig,
    ):
        """
        初始化笔对象
        
        Args:
            pre: 前一个笔对象
            start: 起始分型
            end: 结束分型
            elements: 组成笔的K线列表
            fake: 是否为虚笔，虚笔不满足最低长度要求
            config: 缠论配置对象
        """
        super().__init__(start, end, 0, elements, "Bi")
        self.pre = pre
        self.fake = fake
        self.config = config

        if pre is not None:
            assert pre.end is start, (pre.end, start)
            self.index = pre.index + 1

    def __str__(self):
        """返回笔的字符串表示"""
        return f"Bi({self.index}, {self.direction}, {colored(self.start.dt, 'green')}, {self.start.speck}, {colored(self.end.dt, 'green')}, {self.end.speck}, {self.elements[-1]}, fake: {self.fake})"

    def __repr__(self):
        """返回笔的字符串表示，用于调试和打印"""
        return f"Bi({self.index}, {self.direction}, {colored(self.start.dt, 'green')}, {self.start.speck}, {colored(self.end.dt, 'green')}, {self.end.speck}, {self.elements[-1]}, fake: {self.fake})"

    @property
    def length(self) -> int:
        """
        获取笔的长度
        根据配置计算笔包含的实际K线数量，考虑跳空因素
        
        Returns:
            笔的实际长度
        """
        size = 1
        elements = self.elements
        for i in range(1, len(elements)):
            left = elements[i - 1]
            right = elements[i]
            assert left.index + 1 == right.index, (
                left.index,
                right.index,
            )
            relation = double_relation(left, right)
            if self.config.BI_JUMP and relation.is_jump():
                if self.config.BI_JUMP_SCALE > 0.0:
                    if relation.is_up():
                        high = right.low
                        low = left.high
                    else:
                        high = left.low
                        low = right.high

                    real_high = self.real_high
                    real_low = self.real_low
                    if (high - low) / (real_high.high - real_low.low) >= self.config.BI_JUMP_SCALE:
                        size += 1

                else:
                    size += 1
            size += 1
        if not self.config.BI_JUMP:
            assert size == len(elements)
        if self.config.BI_JUMP:
            return size
        return len(elements)

    @property
    def real_high(self) -> Optional[Bar]:
        """
        获取笔中的实际最高点K线
        根据配置决定取首个或最后一个最高点
        
        Returns:
            笔中的最高点K线
        """
        if not self.elements:
            return None
        highs: List[Bar] = [self.elements[0]]
        for bar in self.elements[1:]:
            if bar.high >= highs[-1].high:
                if bar.high > highs[-1].high:
                    highs.clear()
                highs.append(bar)
        if len(highs) > 1:
            dp("", highs)
        return highs[-1] if self.config.BI_LASTorFIRST else highs[0]

    @property
    def real_low(self) -> Optional[Bar]:
        """
        获取笔中的实际最低点K线
        根据配置决定取首个或最后一个最低点
        
        Returns:
            笔中的最低点K线
        """
        if not self.elements:
            return None
        lows: List[Bar] = [self.elements[0]]
        for bar in self.elements[1:]:
            if bar.low <= lows[-1].low:
                if bar.low < lows[-1].low:
                    lows.clear()
                lows.append(bar)
        if len(lows) > 1:
            dp("", lows)
        return lows[-1] if self.config.BI_LASTorFIRST else lows[0]

    @property
    def relation(self) -> bool:
        """
        判断笔的起始点和终点关系是否符合要求
        根据配置和笔的方向进行判断
        
        Returns:
            如果关系符合要求返回True，否则返回False
        """
        if self.config.BI_FENGXING:
            start = self.start
            relation = double_relation(start, self.end)
        else:
            start = self.start.mid
            relation = double_relation(start, self.end)

        if self.direction is Direction.Down:
            return relation.is_down()
        return relation.is_jump()

    def check(self) -> bool:
        """
        检查笔是否有效
        验证笔的长度和起止点是否满足缠论定义
        
        Returns:
            如果笔有效返回True，否则返回False
        """
        if len(self.elements) >= self.config.BI_FENGXING:
            # assert self.start.mid is self.elements[0]
            # assert self.end.mid is self.elements[-1]
            if self.direction is Direction.Down and self.start.mid is self.real_high and self.end.mid is self.real_low:
                return True
            if self.direction is Direction.Up and self.start.mid is self.real_low and self.end.mid is self.real_high:
                return True
        return False

    @staticmethod
    def get_elements(bars: List[Bar], start: FenXing, end: FenXing) -> List[Bar]:
        """
        获取笔中包含的K线列表
        从起始分型到结束分型之间的所有K线
        
        Args:
            bars: 完整的K线列表
            start: 起始分型
            end: 结束分型
            
        Returns:
            笔包含的K线列表
        """
        return bars[bars.index(start.mid) : bars.index(end.mid) + 1]

    @classmethod
    def analyzer(
        cls,
        fx: FenXing,
        fxs: List[FenXing],
        bis: List["Bi"],
        bars: List[Bar],
        _from: str,
        level: int,
        config: ChanConfig,
        observer: Observer,
    ):
        """
        分析笔
        核心方法，根据新的分型更新笔的列表
        
        Args:
            fx: 新的分型
            fxs: 分型列表
            bis: 笔列表
            bars: K线列表
            _from: 调用源标识
            level: 递归级别
            config: 缠论配置
            observer: 观察者对象，用于通知UI更新
        """
        if not fxs:
            if fx.shape in (Shape.G, Shape.D):
                fxs.append(fx)
            return

        def pop():
            tmp_ = fxs.pop()
            if bis:
                bi_ = bis.pop()
                assert bi_.end is tmp_, "最后一笔终点错误"
                if _from == "analyzer":
                    bdp(f"Bi. pop: {bi_}")
                    observer and observer.notify(bi_, Command.Remove("Bi"))

        last = fxs[-1]

        if last.mid.dt > fx.mid.dt:
            raise ChanException(f"时序错误 last.mid.dt:{last.mid.dt} fx.mid.dt:{fx.mid.dt}")

        if (last.shape is Shape.G and fx.shape is Shape.D) or (last.shape is Shape.D and fx.shape is Shape.G):
            bi = Bi(None, last, fx, Bi.get_elements(bars, last, fx), False, config)
            if bi.length > 4:
                eq = config.BI_LASTorFIRST
                config.BI_LASTorFIRST = False  # 起始点检测时不考虑相同起始点情况，避免递归

                if last.shape is Shape.G and fx.shape is Shape.D:
                    start = bi.real_high
                else:
                    start = bi.real_low
                if start is not last.mid:
                    # print("不是真底")
                    new = FenXing.get_fenxing(bars, start)
                    if last.shape is Shape.G and fx.shape is Shape.D:
                        assert new.shape is Shape.G, new
                    else:
                        assert new.shape is Shape.D, new
                    Bi.analyzer(new, fxs, bis, bars, _from, level + 1, config, observer)  # 处理新顶
                    Bi.analyzer(fx, fxs, bis, bars, _from, level + 1, config, observer)  # 再处理当前底
                    config.BI_LASTorFIRST = eq
                    return
                config.BI_LASTorFIRST = eq

                if last.shape is Shape.G and fx.shape is Shape.D:
                    end = bi.real_low
                else:
                    end = bi.real_high

                if bi.relation and fx.mid is end:
                    FenXing.append(fxs, fx)
                    Line.append(bis, bi)
                    if _from == "analyzer":
                        bdp(f"Bi. append: {bi}")
                        observer and observer.notify(bi, Command.Append("Bi"))
                else:
                    # 2024 05 21 修正
                    if len(fxs) < 3:
                        return
                    _bars = bars[bars.index(last.mid) :]
                    _fx, _bi = Bi.analysis_one(_bars, level, config, observer)
                    if _bi is None:
                        return

                    start = fxs[-3]
                    end = _bi.start
                    nb = Bi(None, start, end, Bi.get_elements(bars, start, end), False, config)
                    if not nb.check():
                        return
                    # print(_bi)
                    pop()
                    Bi.analyzer(_bi.start, fxs, bis, bars, _from, level + 1, config, observer)

            else:
                ...
                # GD or DG
                if (last.shape is Shape.G and fx.shape is Shape.D and fx.right.high > last.speck) or (last.shape is Shape.D and fx.shape is Shape.G and fx.right.low < last.speck):
                    pop()

        elif (last.shape is Shape.G and (fx.shape is Shape.S or fx.shape is Shape.G)) or (last.shape is Shape.D and (fx.shape is Shape.X or fx.shape is Shape.D)):
            if last.shape is Shape.G:
                func = min

                def okey(o):
                    return o.low
            else:
                func = max

                def okey(o):
                    return o.high

            if fx.shape is Shape.S:
                speck = fx.right.high
            elif fx.shape is Shape.X:
                speck = fx.right.low
            else:
                speck = fx.speck

            if (last.shape is Shape.G and last.speck < speck) or (last.shape is Shape.D and last.speck > speck):
                pop()
                if fxs:
                    last = fxs[-1]
                    if fx.shape is Shape.S or fx.shape is Shape.G:
                        assert last.shape is Shape.D, last.shape
                    else:
                        assert last.shape is Shape.G, last.shape

                    new = FenXing.get_fenxing(
                        bars,
                        func(
                            Bi.get_elements(bars, last, fx),
                            key=okey,
                        ),
                    )

                    if fx.shape is Shape.S or fx.shape is Shape.G:
                        assert new.shape is Shape.D
                    else:
                        assert new.shape is Shape.G

                    if (last.shape is Shape.G and last.speck > new.mid.low) or (last.shape is Shape.D and last.speck < new.mid.high):
                        pop()
                        Bi.analyzer(new, fxs, bis, bars, _from, level + 1, config, observer)  # 处理新底
                        # print("GS修正") or print("DX修正")
                        if fx.shape in (Shape.S, Shape.X):
                            return
                        Bi.analyzer(fx, fxs, bis, bars, _from, level + 1, config, observer)  # 再处理当前顶
                        # print("GG修正") or print("DD修正")
                        return

                if fx.shape in (Shape.S, Shape.X):
                    return

                if not fxs:
                    FenXing.append(fxs, fx)
                    return

                bi = Bi(None, last, fx, Bi.get_elements(bars, last, fx), False, config)

                FenXing.append(fxs, fx)
                Line.append(bis, bi)
                if _from == "analyzer":
                    bdp(f"Bi. append: {bi}")
                    observer and observer.notify(bi, Command.Append("Bi"))

        elif (last.shape is Shape.G and fx.shape is Shape.X) or (last.shape is Shape.D and fx.shape is Shape.S):
            ...

        else:
            raise ChanException(last.shape, fx.shape)

    @staticmethod
    def analysis_one(bars: List[Bar], level: int, config: ChanConfig, observer: Observer) -> tuple[Optional[FenXing], Optional["Bi"]]:
        """
        分析单一序列生成一笔
        尝试从K线序列中识别第一个笔
        
        Args:
            bars: K线列表
            level: 递归级别
            config: 缠论配置
            observer: 观察者对象
            
        Returns:
            元组，包含找到的分型和笔，如果没有找到则返回None
        """
        try:
            bars[2]
        except IndexError:
            return None, None
        bis = []
        fxs = []
        fx = None
        size = len(bars)
        for i in range(1, size - 2):
            left, mid, right = bars[i - 1], bars[i], bars[i + 1]
            fx = FenXing(left, mid, right)
            Bi.analyzer(fx, fxs, bis, bars, "tmp", level + 1, config, observer)
            if bis:
                return fx, bis[0]
        if bis:
            return fx, bis[0]
        return None, None


@final
class Duan(Line):
    """
    线段类
    缠论分析中的次级别结构，由多个同向笔组成
    表示价格在一个方向上的完整运动，通常由特征序列构成
    是中枢和走势类型分析的基础
    """
    __slots__ = "features", "observer"

    def __init__(
        self,
        start: FenXing,
        end: FenXing,
        elements: List[Line],
        stamp: str = "Duan",
        *,
        observer: Optional[Observer] = None,
    ):
        """
        初始化线段对象
        
        Args:
            start: 起始分型
            end: 结束分型
            elements: 组成线段的笔列表
            stamp: 标识符，通常为"Duan"或笔标识+"Duan"
            observer: 观察者对象，用于通知UI更新
        """
        super().__init__(start, end, 0, elements, stamp)
        self.observer: Optional[Observer] = observer
        self.features: list[Optional[FeatureSequence]] = [None, None, None]  # 线段的三个特征序列（左中右）

    def __str__(self):
        """返回线段的字符串表示"""
        return f"{self.stamp}({self.index}, {self.direction}, has pre: {self.pre is not None}, done: {self.done}, {self.state}, {self.start}, {self.end}, size={len(self.elements)})"

    def __repr__(self):
        """返回线段的字符串表示，用于调试和打印"""
        return str(self)

    @property
    def gap(self) -> Optional[Pillar]:
        """
        获取线段之间的缺口
        当左特征序列和中特征序列之间存在跳空时返回缺口对象
        
        Returns:
            缺口对象，如果不存在则返回None
        """
        if not self.mid:
            return
        if double_relation(self.left, self.mid).is_jump():
            hl = [self.left.start.speck, self.mid.start.speck]
            return Pillar(max(*hl), min(*hl))

    @property
    def done(self) -> bool:
        """
        判断线段是否完成
        当存在右特征序列时，表示线段已完成
        
        Returns:
            如果线段已完成则返回True，否则返回False
        """
        return self.right is not None

    @property
    def lmr(self) -> tuple[bool, bool, bool]:
        """
        获取线段三个特征序列的存在状态
        
        Returns:
            三元组，分别表示左、中、右特征序列是否存在
        """
        return self.left is not None, self.mid is not None, self.right is not None

    @property
    def state(self) -> Optional[str]:
        """
        获取线段的状态描述
        根据前一线段是否有缺口和当前线段的方向确定状态
        
        Returns:
            线段状态描述："老阳"、"老阴"、"小阳"或"少阴"
        """
        if self.pre is not None and self.pre.gap:
            return "老阳" if self.direction is Direction.Up else "老阴"
        return "小阳" if self.direction is Direction.Up else "少阴"

    @property
    def left(self) -> FeatureSequence:
        """获取左特征序列"""
        return self.features[0]

    @left.setter
    def left(self, feature: FeatureSequence):
        """设置左特征序列"""
        self.__feature_setter(0, feature)

    @property
    def mid(self) -> FeatureSequence:
        """获取中特征序列"""
        return self.features[1]

    @mid.setter
    def mid(self, feature: FeatureSequence):
        """设置中特征序列"""
        self.__feature_setter(1, feature)

    @property
    def right(self) -> FeatureSequence:
        """获取右特征序列"""
        return self.features[2]

    @right.setter
    def right(self, feature: FeatureSequence):
        """设置右特征序列"""
        self.__feature_setter(2, feature)

    def __feature_setter(self, offset: int, feature: Optional[FeatureSequence]):
        """
        设置特征序列并通知观察者
        
        Args:
            offset: 特征序列索引（0:左, 1:中, 2:右）
            feature: 要设置的特征序列对象
            
        Raises:
            ChanException: 如果特征序列方向与线段方向相同
        """
        if feature and feature.direction == self.direction:
            raise ChanException("特征序列方向不匹配")
        features: List = self.features
        observer: Optional[Observer] = self.observer
        old = features[offset]
        features[offset] = feature

        old and observer and observer.notify(old, Command.Remove(old.stamp))
        feature and observer and observer.notify(feature, Command.Append(feature.stamp))

    def clear_features(self):
        """
        清除线段的所有特征序列
        并通知观察者移除特征序列
        """
        for feature in self.features:
            if feature is not None:
                self.observer and self.observer.notify(feature, Command.Remove(feature.stamp))

    def update(self, lines: List[Line]) -> bool:
        """
        更新线段，添加新的笔
        
        Args:
            lines: 笔列表
            
        Returns:
            更新后线段是否完成
            
        Raises:
            AssertionError: 如果线段未完成
        """
        assert self.done is True, (self, self.features)
        i = self.elements[-1].index
        while 1:
            try:
                lines.index(self.elements[-1])
                break
            except ValueError:
                self.pop_element(self.elements[-1])

        for line in lines:
            if self.elements[-1].is_next(line):
                self.add_element(line)
                if line.index == i:
                    break
        # assert size == len(self.elements)
        return self.done

    def get_next_elements(self) -> List[Line]:
        """
        获取以线段结束点为起点的后续线对象
        
        Returns:
            后续线对象列表
            
        Raises:
            AssertionError: 如果第一个元素的起点不是线段的起点
        """
        assert self.elements[0].start is self.start, (self.elements[0].start, self.start)
        elements = []
        for line in self.elements:
            if elements:
                elements.append(line)
            if line.start is self.end:
                elements.append(line)
        return elements

    def set_elements(self, elements: List[Line]):
        """
        设置线段的组成元素
        
        Args:
            elements: 线对象列表
            
        Raises:
            AssertionError: 如果第一个元素的起点不是线段的起点
        """
        assert elements[0].start is self.start, (elements[0].start, self.start)
        self.clear_features()
        self.elements.clear()
        last = None
        for i in range(1, len(elements) - 1):
            pre = elements[i - 1]
            last = elements[i]
            assert last.is_previous(pre) is True
            self.add_element(pre)
            if self.done:
                print("set_elements done", i, len(elements))
        if last:
            self.add_element(last)

    def get_elements(self) -> List[Line]:
        """
        获取线段的组成元素到结束点
        
        Returns:
            线段的组成元素列表
            
        Raises:
            AssertionError: 如果第一个元素的起点不是线段的起点
        """
        assert self.elements[0].start is self.start, (self.elements[0].start, self.start)
        elements = []
        for obj in self.elements:
            elements.append(obj)
            if obj.end is self.end:
                break
        return elements

    def pop_element(self, line: Line) -> Line:
        """
        从线段中移除一个线对象
        并重新分析特征序列
        
        Args:
            line: 要移除的线对象
            
        Returns:
            被移除的线对象
        """
        duan = self
        drop = Line.pop(duan.elements, line)
        duan.left, duan.mid, duan.right = FeatureSequence.analyzer(duan.elements, duan.direction)
        return drop

    def add_element(self, line: Line):
        """
        向线段添加一个线对象
        并重新分析特征序列和更新终点
        
        Args:
            line: 要添加的线对象
        """
        duan = self
        Line.append(duan.elements, line)
        if self.done:
            ...

        duan.left, duan.mid, duan.right = FeatureSequence.analyzer(duan.elements, duan.direction)
        if duan.mid is not None:
            duan.end = duan.mid.start

        if duan.direction == line.direction:
            if duan.mid is not None:
                if duan.direction == Direction.Up:
                    if duan.high < line.high:
                        duan.end = line.end
                    else:
                        duan.end = duan.mid.start
                else:
                    if duan.low > line.low:
                        duan.end = line.end
                    else:
                        duan.end = duan.mid.start
            else:
                duan.end = line.end

    @classmethod
    def new(cls, line: Line | List[Line], observer: Optional[Observer]) -> "Duan":
        """
        创建新的线段对象
        
        Args:
            line: 单个线对象或线对象列表
            observer: 观察者对象，用于通知UI更新
            
        Returns:
            创建的线段对象
        """
        if type(line) is list:
            lines = line[:]
            return Duan(line[0].start, line[2].end, lines, "Duan" if lines[0].stamp == "Bi" else lines[0].stamp + "Duan", observer=observer)
        return Duan(line.start, line.end, [line], "Duan" if line.stamp == "Bi" else line.stamp + "Duan", observer=observer)

    @classmethod
    def analyzer(cls, lines: List[Line], xds: List["Duan"], observer: Observer):
        """
        分析线段
        从线对象列表中分析提取线段
        这是缠论中线段识别的核心算法
        
        Args:
            lines: 线对象列表（通常是笔列表）
            xds: 已识别的线段列表
            observer: 观察者对象，用于通知UI更新
        """
        if not lines:
            return
        try:
            lines[5]
        except IndexError:
            return

        if not xds:
            for i in range(1, len(lines) - 1):
                left, mid, right = lines[i - 1], lines[i], lines[i + 1]
                if double_relation(left, right).is_jump():
                    continue
                duan = Duan.new([left, mid, right], observer)
                Line.append(xds, duan)
                observer and observer.notify(duan, Command.Append(duan.stamp))
                return Duan.analyzer(lines, xds, observer)

        else:
            last = xds[-1]
            while 1:
                try:
                    index = lines.index(last.elements[-1]) + 1
                    break
                except ValueError:
                    line = last.pop_element(last.elements[-1])
                    ddp("Duan.analyzer 弹出", line)

                    if not last.elements:
                        print("Duan.analyzer 无法找到", last)
                        if Line.pop(xds, last) is not None:
                            observer and observer.notify(last, Command.Remove(last.stamp))
                            last.clear_features()
                        return Duan.analyzer(lines, xds, observer)
            duan = last

            # for line in lines[index:]:
            for i in range(index, len(lines)):
                line = lines[i]
                last = duan.pre
                if last and last.elements[-1] not in lines:
                    if not last.update(lines):
                        # print("异常", last)
                        Line.pop(xds, duan)
                        observer and observer.notify(duan, Command.Remove(duan.stamp))
                        duan.clear_features()
                        return Duan.analyzer(lines, xds, observer)

                if last and last.gap and len(duan.elements) == 3:
                    if (last.direction is Direction.Up and line.high > last.high) or (last.direction is Direction.Down and line.low < last.low):
                        Line.pop(xds, duan)
                        observer and observer.notify(duan, Command.Remove(duan.stamp))
                        duan.clear_features()
                        last.add_element(line)
                        observer and observer.notify(last, Command.Modify(last.stamp))
                        # print("修正")
                        duan = last
                        continue

                duan.add_element(line)
                observer and observer.notify(duan, Command.Modify(duan.stamp))
                if duan.done:
                    elements = duan.get_next_elements()
                    duan.clear_features()
                    for feature in duan.features:
                        if feature is not None:
                            observer and observer.notify(feature, Command.Append(feature.stamp))

                    if duan.direction is Direction.Up:
                        fx = "顶分型"
                    else:
                        fx = "底分型"

                    ddp("    ", f"{fx}终结, 缺口: {duan.gap}")
                    size = len(elements)
                    if size >= 3:
                        duan = Duan.new(elements[:3], observer)
                        Line.append(xds, duan)
                        observer and observer.notify(duan, Command.Append(duan.stamp))
                        for feature in duan.features:
                            if feature is not None:
                                observer and observer.notify(feature, Command.Append(feature.stamp))

                        return Duan.analyzer(lines, xds, observer)

                    duan = Duan.new(elements, observer)
                    Line.append(xds, duan)
                    observer and observer.notify(duan, Command.Append(duan.stamp))
                    for feature in duan.features:
                        if feature is not None:
                            observer and observer.notify(feature, Command.Append(feature.stamp))


class BaseAnalyzer(Observer):
    """
    缠论基础分析器
    整个缠论分析系统的核心类，负责整合和管理所有缠论元素
    包括K线、分型、笔、线段、中枢等各级别分析对象的生成和计算
    """
    # !! 修改 __slots__ 添加 freq_str !!
    __slots__ = "symbol", "freq", "ws", "last_raw_bar", "raws", "news", "fxs", "bis", "xds", "bzss", "dzss", "cache", "config", "bi_bs_points", "duan_bs_points", "zs", "freq_str"

    def __init__(self, symbol: str, freq: Union[SupportsInt, str], ws: WebSocket = None): # 允许 freq 是字符串
        """
        初始化分析器
        
        Args:
            symbol: 分析标的代码，如股票代码或期货合约代码
            freq: 分析周期，可以是整数秒数或字符串形式周期
            ws: WebSocket连接，用于实时推送分析结果
        """
        self.symbol: str = symbol
        self.ws = ws

        # 处理传入的 freq (可能是 int 或 str)
        if isinstance(freq, str):
            self.freq_str: str = freq.lower() # 存储字符串形式 (统一小写)
            # 尝试从映射转换回整数秒数
            self.freq: int = PERIOD_STRING_TO_SECONDS.get(self.freq_str)
            if self.freq is None:
                print(f"警告: 未知的周期字符串 '{freq}'，无法转换为秒数。将 freq 设为 0。")
                self.freq = 0 # 或者抛出错误，或者设置默认值
        elif isinstance(freq, SupportsInt):
            self.freq: int = int(freq) # 存储整数秒数
            # 尝试从秒数找到对应的标准字符串表示 (可选)
            found_str = None
            for key, value in PERIOD_STRING_TO_SECONDS.items():
                if value == self.freq:
                    found_str = key
                    break
            self.freq_str: str = found_str if found_str else str(self.freq) # 存储字符串形式
        else:
             raise TypeError(f"不支持的 freq 类型: {type(freq)}")

        print(f"BaseAnalyzer initialized: symbol={self.symbol}, freq(seconds)={self.freq}, freq_str={self.freq_str}")

        # 数据容器初始化
        self.last_raw_bar: Optional[Bar] = None  # 最后一根原始K线
        self.raws: list[Bar] = []  # 原始K线列表
        self.news: list[Bar] = []  # 合并后的K线列表
        self.fxs: list[FenXing] = []  # 分型列表
        self.bis: list[Bi] = []  # 笔列表
        self.xds: list[Duan] = []  # 线段列表
        self.bzss: list[ZhongShu] = []  # 笔中枢列表
        self.dzss: list[ZhongShu] = []  # 段中枢列表
        self.cache = dict()  # 缓存数据
        self.config = ChanConfig()  # 缠论配置
        self.zs = []  # 用于Interval分析
        # 买卖点列表初始化
        self.bi_bs_points: list[BSPoint] = []  # 笔级别买卖点
        self.duan_bs_points: list[BSPoint] = []  # 段级别买卖点

    def check_macd_divergence(self, line: Line, prev_line: Line) -> bool:
        """
        检查是否存在MACD背离
        当价格创新高/新低时，MACD没有同步创新高/新低则形成背离
        
        Args:
            line: 当前线段
            prev_line: 前一线段
            
        Returns:
            是否存在背离
        """
        # 必须有两条线才能检查背离
        if not line or not prev_line:
            return False
            
        # 确保方向相同
        if line.direction != prev_line.direction:
            return False
            
        # 获取两条线的MACD数据
        line_macd = line.calc_macd()
        prev_macd = prev_line.calc_macd()
        
        # 检查方向向上时的顶背离
        if line.direction == Direction.Up:
            # 价格创新高但MACD未创新高
            if line.high > prev_line.high and abs(line_macd["up"]) <= abs(prev_macd["up"]):
                return True
        # 检查方向向下时的底背离
        elif line.direction == Direction.Down:
            # 价格创新低但MACD未创新低
            if line.low < prev_line.low and abs(line_macd["down"]) <= abs(prev_macd["down"]):
                return True
                
        return False
    
    def _find_last_bs_point(self, points_list: list[BSPoint], info_type: str, point_type_prefix: str) -> Optional[BSPoint]:
        """
        查找特定类型的最后一个买卖点
        
        Args:
            points_list: 买卖点列表
            info_type: 'Bi' 或 'Duan'
            point_type_prefix: 'First', 'Second', 'Third'
            
        Returns:
            最后一个匹配的买卖点或None
        """
        for point in reversed(points_list):
            if point.info == info_type and point_type_prefix in point.tp:
                return point
        return None
        
    def _add_bs_point(self, info: str, tp: str, dt: datetime, price: float, valid: bool, creation_offset: int, fix_offset: int):
        """
        添加一个买卖点并发送通知
        
        Args:
            info: 'Bi' 或 'Duan'
            tp: 买卖点类型，如 'FirstBuy'
            dt: 买卖点的时间
            price: 买卖点的价格
            valid: 该买卖点是否有效
            creation_offset: 创建买卖点的线的索引
            fix_offset: 固定买卖点的线的索引
            
        Returns:
            创建的买卖点对象
        """
        stamp = f"{info}_{tp}_{int(dt.timestamp())}"
        point = BSPoint(info, tp, dt, price, valid, creation_offset, fix_offset, stamp)
        
        # 添加到相应的列表
        if info == 'Bi':
            self.bi_bs_points.append(point)
        else:  # 'Duan'
            self.duan_bs_points.append(point)
            
        # 发送通知
        self.notify(point, Command.Append(stamp))
        return point
        
    def analyze_bs_points(self):
        """
        分析并标记买卖点
        1. 第一类买卖点：通过背离判断
        2. 第二类买卖点：第一类买点后的第一次回调不创新低
        3. 第三类买卖点：突破中枢后回调不回到中枢
        """
        # 确保有足够的笔或段
        if len(self.bis) < 3:
            return
            
        # 分析笔级别买卖点
        self._analyze_level_bs(self.bis, self.bi_bs_points, 'Bi')
        
        # 如果有段，则分析段级别买卖点
        if len(self.xds) >= 3:
            self._analyze_level_bs(self.xds, self.duan_bs_points, 'Duan')
            
    def _analyze_level_bs(self, lines: List[Line], points_list: List[BSPoint], level: str):
        """
        分析特定级别（笔或段）的买卖点
        
        Args:
            lines: 线的列表（笔或段）
            points_list: 买卖点列表
            level: 'Bi' 或 'Duan'
        """
        # 至少需要两条线才能进行分析
        if len(lines) < 2:
            return
            
        # 获取最后和倒数第二条线
        current_line = lines[-1]
        prev_line = lines[-2]
        
        # 创建买卖点的条件
        create_bs_point = False
        point_type = ""
        
        # 检查第一类买卖点（通过背离）
        if len(lines) >= 3:
            pprev_line = lines[-3]
            # print(f"--- {level} 检查 T1 ---") # 添加日志
            # print(f"  Current: {current_line}") # 添加日志
            # print(f"  Prev:    {prev_line}") # 添加日志
            # print(f"  PPrev:   {pprev_line}") # 添加日志

            # --- 修改：检查 current_line 和 pprev_line 是否同向 ---
            if current_line.direction == pprev_line.direction:
                # --- 修改：使用 current_line 和 pprev_line 进行背离检查 ---
                divergence_found = self.check_macd_divergence(current_line, pprev_line)
                # print(f"  同向({current_line.direction})，检查 current 与 pprev 背离结果: {divergence_found}") # 修改日志
                if divergence_found:
                    if current_line.direction == Direction.Up:
                        point_type = "FirstSell"
                        price = current_line.high
                    else:
                        point_type = "FirstBuy"
                        price = current_line.low

                    # 创建第一类买卖点
                    # print(f"  准备添加 T1: {level} {point_type}") # 添加日志
                    self._add_bs_point(
                        level, point_type,
                        current_line.end.dt, price,
                        True, current_line.index, current_line.index
                    )
            # --- 修改结束 ---

        # 检查第二类买卖点（第一类买点后的第一次回调不创新低）
        # 当前线与前一条线方向相反
        if current_line.direction != prev_line.direction:
            # print(f"--- {level} 检查 T2 ---") # 添加日志
            # 查找最近的第一类买点
            last_first_point = self._find_last_bs_point(points_list, level, "First")
            # print(f"  找到最近的 T1 点: {last_first_point}") # 添加日志

            if last_first_point:
                 if current_line.index > last_first_point.creation_offset:
                    # 第二类买点：向下回调不创新低
                    # print(f"  检查 T2 买: 回调低点({current_line.low:.2f}) > T1 买点价格({last_first_point.price:.2f}) ? {current_line.low > last_first_point.price}") # 添加日志
                    if current_line.low > last_first_point.price:
                        # print(f"  准备添加 T2 买: {level} SecondBuy") # 添加日志
                        self._add_bs_point(
                            level, "SecondBuy", 
                            current_line.end.dt, current_line.low, 
                            True, current_line.index, current_line.index
                        )
                    # 第二类卖点：向上回调不创新高
                    elif "Sell" in last_first_point.tp and current_line.direction == Direction.Up:
                        # print(f"  检查 T2 卖: 反弹高点({current_line.high:.2f}) < T1 卖点价格({last_first_point.price:.2f}) ? {current_line.high < last_first_point.price}") # 添加日志
                        if current_line.high < last_first_point.price:
                            # print(f"  准备添加 T2 卖: {level} SecondSell") # 添加日志
                            self._add_bs_point(
                                level, "SecondSell", 
                                current_line.end.dt, current_line.high, 
                                True, current_line.index, current_line.index
                            )
        
        # 检查第三类买卖点（突破中枢后回调不回到中枢）
        # 需要有中枢
        zss = self.bzss if level == 'Bi' else self.dzss
        if zss and len(lines) >= 3:
            last_zs = zss[-1]
            
            # 如果当前线与前一条线方向相反
            if current_line.direction != prev_line.direction:
                # 当前线是下跌
                if current_line.direction == Direction.Down:
                    # 前一条线突破了中枢上沿
                    if prev_line.high > last_zs.zg:
                        # 当前回调没有回到中枢区间
                        if current_line.low > last_zs.zg:
                            self._add_bs_point(
                                level, "ThirdBuy", 
                                current_line.end.dt, current_line.low, 
                                True, current_line.index, current_line.index
                            )
                # 当前线是上涨
                elif current_line.direction == Direction.Up:
                    # 前一条线突破了中枢下沿
                    if prev_line.low < last_zs.zd:
                        # 当前回调没有回到中枢区间
                        if current_line.high < last_zs.zd:
                            self._add_bs_point(
                                level, "ThirdSell", 
                                current_line.end.dt, current_line.high, 
                                True, current_line.index, current_line.index
                            )

    def notify(self, obj: Any, cmd: Command):
        """
        通知UI更新
        实现Observer抽象基类的方法，用于将变化通知给前端界面
        
        Args:
            obj: 变更的对象
            cmd: 操作命令
        """
        if not self.config.ANALYZER_SHON_TV:
            return
        message = dict()
        message["stamp"] = obj.stamp if hasattr(obj, "stamp") else obj.__class__.__name__

        if type(obj) is Bar:
            message["type"] = "realtime"
            message["timestamp"] = obj.dt.strftime("%Y-%m-%d %H:%M:%S")  # 使用标准格式，确保包含时间信息
            message["open"] = obj.open
            message["high"] = obj.high
            message["low"] = obj.low
            message["close"] = obj.close
            message["volume"] = obj.volume

        if type(obj) is Bi:
            message["type"] = "shape"
            message["cmd"] = str(cmd)
            message["id"] = str(hash(obj))
            message["name"] = "trend_line"
            message["points"] = [{"time": int(obj.start.dt.timestamp()), "price": obj.start.speck}, {"time": int(obj.end.dt.timestamp()), "price": obj.end.speck}]
            message["options"] = {"shape": "trend_line", "text": obj.stamp}
            message["properties"] = {"linecolor": "#CC62FF", "linewidth": 2, "title": f"{obj.stamp}-{obj.index}"}

            if cmd.cmd == Command.APPEND:
                ...
            elif cmd.cmd == Command.MODIFY:
                ...
            elif cmd.cmd == Command.REMOVE:
                ...

        if type(obj) is Duan:
            message["type"] = "shape"
            message["cmd"] = str(cmd)
            message["id"] = str(id(obj))
            message["name"] = "trend_line"
            message["points"] = [{"time": int(obj.start.dt.timestamp()), "price": obj.start.speck}, {"time": int(obj.end.dt.timestamp()), "price": obj.end.speck}]
            message["options"] = {"shape": "trend_line", "text": obj.stamp}
            message["properties"] = {"linecolor": "#F1C40F" if obj.stamp == "Duan" else "#00C40F", "linewidth": 3, "title": f"{obj.stamp}-{obj.index}", "text": obj.stamp}

        if type(obj) is Interval:
            message["type"] = "shape"
            message["cmd"] = str(cmd)
            message["id"] = str(id(obj))
            message["name"] = "rectangle"
            message["points"] = [{"time": int(obj.elements[0].dt.timestamp()), "price": obj.high}, {"time": int(obj.elements[-1].dt.timestamp()), "price": obj.low}]
            message["options"] = {"shape": "rectangle", "text": "nb"}
            message["properties"] = {"color": "#00C40F", "backgroundColor": "#00C40F"}

        if type(obj) is ZhongShu:
            message["type"] = "shape"
            message["cmd"] = str(cmd)
            message["id"] = str(hash(obj))
            message["name"] = "rectangle"
            if cmd.cmd == Command.APPEND or cmd.cmd == Command.MODIFY:
                points = (
                    [
                        {"time": int(obj.start.dt.timestamp()), "price": obj.zg},
                        {
                            "time": int(obj.elements[-1].end.mid.dt.timestamp()),
                            "price": obj.zd,
                        },
                    ]
                    if len(obj.elements) <= 3
                    else [
                        {"time": int(obj.start.dt.timestamp()), "price": obj.zg},
                        {
                            "time": int(obj.elements[-1].start.mid.dt.timestamp()),
                            "price": obj.zd,
                        },
                    ]
                )

            elif cmd.cmd == Command.REMOVE:
                points = []
            else:
                points = []

            message["points"] = points
            message["options"] = {"shape": "rectangle", "text": obj.stamp}
            message["properties"] = {
                "color": "#993333" if obj.direction is Direction.Down else "#99CC99",  # 上下上 为 红色，反之为 绿色
                "linewidth": 1 if obj.elements[0].stamp == "Bi" else 2,
                "title": f"{obj.stamp}-{obj.index}",
                "text": obj.stamp,
            }

        if type(obj) is FeatureSequence:
            message["type"] = "shape"
            message["cmd"] = str(cmd)
            message["id"] = str(id(obj))
            message["name"] = "trend_line"
            start = obj.start.dt
            end = obj.end.dt
            if start > end:
                start, end = end, start
            message["points"] = [{"time": int(start.timestamp()), "price": obj.start.speck}, {"time": int(end.timestamp()), "price": obj.end.speck}]
            message["options"] = {"shape": "trend_line", "text": obj.stamp}
            message["properties"] = {
                "linecolor": "#FFFFFF" if obj.direction.reversal() is Direction.Down else "#fbc02d",
                "linewidth": 4,
                "linestyle": 1,
                # "showLabel": True,
                "title": obj.stamp,
            }

        if cmd is None:
            # 批量推送所有结构
            for bar in self.news:
                self.notify(bar, Command.Append("NewBar"))
            for fx in self.fxs:
                self.notify(fx, Command.Append("FenXing"))
            for bi in self.bis:
                self.notify(bi, Command.Append("Bi"))
            for xd in self.xds:
                self.notify(xd, Command.Append("Duan"))
            for zs in self.bzss:
                self.notify(zs, Command.Append("ZhongShu"))
            for zs in self.dzss:
                self.notify(zs, Command.Append("ZhongShu"))
            for point in getattr(self, 'bi_bs_points', []):
                self.notify(point, Command.Append("BSPoint"))
            for point in getattr(self, 'duan_bs_points', []):
                self.notify(point, Command.Append("BSPoint"))
            return

        if cmd.cmd == Command.APPEND:
            ...
        elif cmd.cmd == Command.MODIFY:
            ...
        elif cmd.cmd == Command.REMOVE:
            ...

        # Add handling for BSPoint notifications
        if type(obj) is BSPoint:
            message["type"] = "shape"
            message["cmd"] = str(cmd)
            # Use a combination of info, type, and time to create a more stable ID
            message["id"] = f"BS_{obj.info}_{obj.tp}_{int(obj.dt.timestamp())}"
            message["name"] = "arrow_up" if "Buy" in obj.tp else "arrow_down"
            # Point location based on time and price
            message["points"] = [{"time": int(obj.dt.timestamp()), "price": obj.price}]

            color = "#FF0000" # Default Red for Sell
            # text = f"{obj.info[0]}{obj.tp[0]}{obj.tp[-3:]}" # e.g., B1Buy, D2Sell # <-- 旧的英文缩写标签

            # --- 新的中文标签生成逻辑 ---
            level_char = '笔' if obj.info == 'Bi' else '段'
            type_map = {'First': '一', 'Second': '二', 'Third': '三'}
            action_char = '买' if 'Buy' in obj.tp else '卖'
            type_num_char = ''
            for key, val in type_map.items():
                if obj.tp.startswith(key):
                    type_num_char = val
                    break
            text = f"{level_char}{type_num_char}{action_char}" # 例如: 笔一买, 段三卖
            # --- 中文标签生成逻辑结束 ---


            if "Buy" in obj.tp:
                color = "#00FF00" # Green for Buy
            elif "Sell" in obj.tp:
                 color = "#FF0000" # Red for Sell

            # Define visibility based on your preference or add logic later
            visible = True

            message["options"] = {
                "shape": "arrow_up" if "Buy" in obj.tp else "arrow_down",
                "text": text # Keep text short for clarity on chart
            }
            message["properties"] = {
                "color": color,
                "title": f"{obj.info}{obj.tp}", # Full title for potential filtering in frontend JS
                "visible": visible,
                # You might want different arrow sizes or styles for different types
                # "size": 4, # Example size property if supported by your frontend shape drawing
            }

            # Send the message via WebSocket
            if self.ws is not None and self.config.ANALYZER_SHON_TV:
                # Ensure event loop is set correctly if running in thread
                try:
                    loop = asyncio.get_event_loop()
                    if loop.is_closed():
                       loop = asyncio.new_event_loop()
                       asyncio.set_event_loop(loop)
                    asyncio.ensure_future(self.ws.send_text(json.dumps(message)))
                except RuntimeError: # If no current event loop
                    loop = asyncio.new_event_loop()
                    asyncio.set_event_loop(loop)
                    asyncio.ensure_future(self.ws.send_text(json.dumps(message)))
            return # Stop further processing for this object type

        # future = asyncio.ensure_future(self.ws.send_text('{"type": "websocket.send", "text": data}'))
        # self.loop.run_until_complete(future)
        if self.ws is not None and self.config.ANALYZER_SHON_TV:
            asyncio.set_event_loop(self.loop)
            asyncio.ensure_future(self.ws.send_text(json.dumps(message)))
        # print(message)
        return

    @final
    def push(self, bar: Bar):
        """
        处理新K线数据并更新分析结构
        这是缠论分析系统的核心方法，每当有新的K线数据到来时被调用
        负责处理包含关系合并、计算分型、笔、线段和中枢等一系列分析步骤
        
        Args:
            bar: 新的K线对象
        """
        # 维护K线序列的连续性，设置新K线的索引
        if self.last_raw_bar is not None:
            bar.index = self.last_raw_bar.index + 1
        self.last_raw_bar = bar
        # self.raws.append(bar)
        
        pre = None
        if self.news:
            # 尝试获取倒数第二根K线作为参考
            try:
                pre = self.news[-2]
            except IndexError:
                pass
                
            # 检查新K线与最后一根K线的包含关系
            nb = Bar.merger(pre, self.news[-1], bar)
            if nb is not None:
                # 如果合并结果不为空，表示不存在包含关系，添加新K线
                # 计算新K线的MACD指标（如果配置允许）
                if self.config.ANALYZER_CALC_MACD:
                    MACD.calc(self.news[-1], nb)
                self.news.append(nb)
            else:
                # 存在包含关系，已在merger方法中处理，更新最后一根K线的MACD
                if self.config.ANALYZER_CALC_MACD and pre:
                    MACD.calc(pre, self.news[-1])
        else:
            # 第一根K线的处理：创建新K线对象并初始化MACD值
            nb = bar.to_new_bar(None)
            nb.macd = MACD(fast_ema=nb.close, slow_ema=nb.close, dif=0.0, dea=0.0, 
                          fastperiod=self.config.MACD_FAST_PERIOD, 
                          slowperiod=self.config.MACD_SLOW_PERIOD, 
                          signalperiod=self.config.MACD_SIGNAL_PERIOD)
            self.news.append(nb)

        # Interval.analyzer(self.news, self.zs, self)

        # 通知观察者新K线已添加，用于更新UI显示
        self.notify(self.news[-1], Command.Append("NewBar"))

        # 尝试获取最新的三根K线进行分型判断
        try:
            left, mid, right = self.news[-3:]
        except ValueError:
            # K线数量不足三根，无法进行分型判断，直接返回
            return

        # 根据三根K线的关系判断中间K线的形态（顶分型、底分型等）
        (shape, _, _) = triple_relation(left, mid, right)
        mid.shape = shape
        fx = FenXing(left, mid, right)  # 创建分型对象
        
        # 发送通知前等待一定时间，避免UI更新过于频繁
        if self.ws is not None and self.config.ANALYZER_SHON_TV:
            time.sleep(self.TIME)

        # 如果配置不计算笔，则直接返回
        if not self.config.ANALYZER_CALC_BI:
            return

        # 根据新的分型更新笔序列
        Bi.analyzer(fx, self.fxs, self.bis, self.news, "analyzer", 0, self.config, self)
        
        # 缓存优化：如果最后一笔没有变化，则跳过后续分析
        if self.bis and self.cache.get("bi", None) is self.bis[-1]:
            return
        if self.bis:
            self.cache["bi"] = self.bis[-1]
            
        # 如果配置计算笔中枢，则更新笔中枢
        if self.config.ANALYZER_CALC_BI_ZS:
            ZhongShu.analyzer(self.bis, self.bzss, self)

        # 如果配置计算线段，则更新线段
        if self.config.ANALYZER_CALC_XD:
            try:
                Duan.analyzer(self.bis, self.xds, self)
            except Exception as e:
                # 发生异常时保存数据，便于调试分析
                traceback.print_exc()
                xds = self.xds[-3:]
                news = self.news[xds[0].start.left.index :]
                Bar.bars_save_as_dat(f"./templates/{self.symbol}_duan_exception-{self.freq}-{int(news[0].dt.timestamp())}-{int(news[-1].dt.timestamp())}.nb", news)
                raise e
            # 如果最后一段未变化，则直接返回
            if self.xds and self.cache.get("xd", None) is self.xds[-1]:
                return
            if self.xds:
                self.cache["xd"] = self.xds[-1]
            # 如果配置计算线段中枢，则更新线段中枢
            if self.config.ANALYZER_CALC_XD_ZS:
                ZhongShu.analyzer(self.xds, self.dzss, self)
                
        # 在最后分析买卖点
        self.analyze_bs_points()

    @classmethod
    def read_from_dat_file(cls, path: str) -> "BaseAnalyzer":
        """
        从.dat文件读取K线数据并创建分析器
        用于从缓存的数据文件中恢复分析状态，常用于回测和调试
        
        Args:
            path: .dat文件路径，文件名格式通常为"{symbol}-{freq}-{start_timestamp}-{end_timestamp}.nb"
            
        Returns:
            创建并加载了数据的BaseAnalyzer对象
        """
        # 从文件名中解析交易品种、时间周期和时间范围
        name = Path(path).name.split(".")[0]
        symbol, freq, s, e = name.split("-")
        size = struct.calcsize(">6d")  # 计算每条K线数据的字节大小
        
        # 创建分析器对象
        obj = cls(symbol, int(freq))
        
        with open(path, "rb") as f:
            # 记录开始时间，用于性能统计
            start = time.time()
            half = start
            length = 0
            
            # 获取文件实际字节大小
            file_size = os.path.getsize(path)
            
            # 使用内存映射方式高效读取文件
            with mmap.mmap(f.fileno(), file_size, access=mmap.ACCESS_READ) as mm:
                # 每次读取一批数据进行处理，提高效率
                while buffer := mm.read(size * 10000):
                    try:
                        # 遍历每条K线数据
                        for i in range(len(buffer) // size):
                            # 从二进制数据还原K线对象
                            bar = Bar.from_be_bytes(buffer[i * size : i * size + size], stamp="RawBar")
                            # 将K线数据推送给分析器处理
                            obj.push(bar)
                            length += 1
                            
                            # 每处理10万条数据打印一次进度信息
                            if length % 100000 == 0:
                                print(length, f" read in {time.time() - start}s")
                                print(f"news:{len(obj.news)}")
                                print(f"bis: {len(obj.bis)}")
                                print(f"xds: {len(obj.xds)}")
                                print(f"bzss:{len(obj.bzss)}")
                                print(f"dzss:{len(obj.dzss)}")
                                print(f"{time.time() - half}s")
                                print(f"{time.time() - start}s")
                                half = time.time()
                    except KeyboardInterrupt:
                        # 允许用户中断处理过程
                        print(traceback.format_exc())
                        break
                        
            # 打印最终的数据加载统计
            print(f"\nnews:{len(obj.news)} read in {time.time() - start}s")
            print(f"bis: {len(obj.bis)}")
            print(f"xds: {len(obj.xds)}")
            print(f"bzss:{len(obj.bzss)}")
            print(f"dzss:{len(obj.dzss)}")
            print(dir(obj.config))

        return obj

    @final
    def step(
        self,
        dt: Union[datetime, int, str], # type: ignore
        open_: Union[float, str],
        high: Union[float, str],
        low: Union[float, str],
        close: Union[float, str],
        volume: Union[float, str],
    ) -> None:
        """
        处理单根K线数据
        将各种格式的K线数据标准化并传递给push方法进行分析
        支持多种时间日期格式输入，自动进行类型转换
        
        Args:
            dt: K线的日期时间，支持datetime对象、时间戳整数或字符串格式
            open_: 开盘价，支持浮点数或字符串
            high: 最高价，支持浮点数或字符串
            low: 最低价，支持浮点数或字符串
            close: 收盘价，支持浮点数或字符串
            volume: 成交量，支持浮点数或字符串
        """
        # 统一处理日期时间格式，将不同格式转换为datetime对象
        if type(dt) is datetime.datetime:
            # 已经是datetime对象，无需转换
            ...
        elif isinstance(dt, str):
            try:
                # 尝试将字符串转换为日期时间
                if dt.isdigit():  # 如果是纯数字字符串（时间戳）
                    dt: datetime.datetime = datetime.datetime.fromtimestamp(int(dt))
                else:
                    # 尝试按照标准格式解析日期时间字符串
                    try:
                        dt: datetime.datetime = datetime.datetime.strptime(dt, "%Y-%m-%d %H:%M:%S")
                    except ValueError:
                        # 第一种格式失败，尝试没有秒的格式
                        dt: datetime.datetime = datetime.datetime.strptime(dt, "%Y-%m-%d %H:%M")
            except ValueError as e:
                # 所有格式都解析失败，记录错误并使用当前时间作为替代
                print(f"时间解析错误: {dt}, {e}")
                dt: datetime.datetime = datetime.datetime.fromtimestamp(int(time.time()))
        elif isinstance(dt, int):
            # 将整数时间戳转换为datetime对象
            dt: datetime.datetime = datetime.datetime.fromtimestamp(dt)
        else:
            # 不支持的日期时间格式
            raise ChanException("类型不支持", type(dt))
            
        # 将所有价格和成交量转换为浮点数
        open_ = float(open_)
        high = float(high)
        low = float(low)
        close = float(close)
        volume = float(volume)

        # 设置默认索引（在push方法中会更新）
        index = 0

        # 创建原始K线对象并传递给push方法进行分析
        last = Bar.creat_raw_bar(
            dt=dt,
            o=open_,
            h=high,
            low=low,
            c=close,
            v=volume,
            i=index,
        )
        self.push(last)


class Generator(BaseAnalyzer):
    """
    K线数据生成器类
    继承自BaseAnalyzer，用于生成模拟K线数据或加载保存的K线数据
    常用于回测、演示和测试场景，可以根据指定点位生成模拟行情
    """
    def __init__(self, symbol: str, freq: int, ws: WebSocket):
        """
        初始化生成器对象
        
        Args:
            symbol: 交易品种代码
            freq: 时间周期，单位秒
            ws: WebSocket连接对象，用于实时数据推送
        """
        super().__init__(symbol, freq, ws)

    def save_nb_file(self):
        """
        保存当前K线数据到文件
        将news列表中的K线数据以二进制格式保存到.nb文件中
        文件路径格式为：./templates/{self.symbol}_{self.freq}.nb
        """
        Bar.bars_save_as_dat(f"./templates/{self.symbol}-{self.freq}-{int(self.news[0].dt.timestamp())}-{int(self.news[-1].dt.timestamp())}.nb", self.news)

    def load_nb_file(self, path: str):
        """
        从文件加载K线数据
        从指定路径的.nb文件中读取K线数据并推送给分析器处理
        
        Args:
            path: .nb文件路径
        """
        with open(path, "rb") as f:
            buffer = f.read()
            size = struct.calcsize(">6d")
            for i in range(len(buffer) // size):
                bar = Bar.from_be_bytes(buffer[i * size : i * size + size])
                self.push(bar)

    def push_new_bar(self, nb: Bar):
        """
        处理新的K线数据
        将新K线添加到列表并执行分析逻辑，包括分型、笔、线段和中枢识别
        这是Generator类的核心方法，每个K线生成后都会调用此方法进行分析
        
        Args:
            nb: 新的K线对象
        """
        # 添加K线到新K线列表
        self.news.append(nb)
        # Interval.analyzer(self.news, self.zs, self)
        
        # 通知UI更新
        self.notify(self.news[-1], Command.Append("NewBar"))
        
        # 尝试获取最后三根K线进行分型判断
        try:
            left, mid, right = self.news[-3:]
        except ValueError:
            # K线数量不足，无法形成分型
            return

        # 计算中间K线的形态（顶分型、底分型等）
        (shape, _, _) = triple_relation(left, mid, right)
        mid.shape = shape
        fx = FenXing(left, mid, right)
        
        # 等待一定时间，避免UI更新过于频繁
        if self.ws is not None and self.config.ANALYZER_SHON_TV:
            time.sleep(self.TIME)

        # 如果配置不计算笔，则退出
        if not self.config.ANALYZER_CALC_BI:
            return

        # 根据新分型更新笔
        Bi.analyzer(fx, self.fxs, self.bis, self.news, "analyzer", 0, self.config, self)
        
        # 如果最后一笔没有变化，则跳过后续分析
        if self.bis and self.cache.get("bi", None) is self.bis[-1]:
            return
        if self.bis:
            self.cache["bi"] = self.bis[-1]
            
        # 如果配置计算笔中枢，则更新笔中枢
        if self.config.ANALYZER_CALC_BI_ZS:
            ZhongShu.analyzer(self.bis, self.bzss, self)

        # 如果配置计算线段，则更新线段
        if self.config.ANALYZER_CALC_XD:
            try:
                Duan.analyzer(self.bis, self.xds, self)
            except Exception as e:
                # 发生异常时保存数据，便于调试分析
                traceback.print_exc()
                xds = self.xds[-3:]
                news = self.news[xds[0].start.left.index :]
                Bar.bars_save_as_dat(f"./templates/{self.symbol}_duan_exception_byGenerator-{self.freq}-{int(news[0].dt.timestamp())}-{int(news[-1].dt.timestamp())}.nb", news)
                raise e
                
            # 如果最后一段未变化，则直接返回
            if self.xds and self.cache.get("xd", None) is self.xds[-1]:
                return
            if self.xds:
                self.cache["xd"] = self.xds[-1]
                
            # 如果配置计算线段中枢，则更新线段中枢
            if self.config.ANALYZER_CALC_XD_ZS:
                ZhongShu.analyzer(self.xds, self.dzss, self)

    @classmethod
    def generator(cls, points: List[int | dict], seconds=300):
        """
        根据指定点生成模拟K线数据
        基于给定的价格点列表，生成符合缠论规则的K线序列
        
        Args:
            points: 价格点列表，可以是整数或包含详细信息的字典
            seconds: K线时间间隔（秒）
            
        Returns:
            生成的K线列表
        """
        news = []

        def append(array, new):
            """
            内部函数：将新K线添加到列表中
            处理包含关系，确保K线序列符合缠论要求
            
            Args:
                array: K线列表
                new: 新K线
            """
            if not array:
                array.append(new)
                return
            if double_relation(array[-1], new) is Direction.Left:
                # 左包含关系，使用新K线替换最后一根
                array[-1] = new
            elif double_relation(array[-1], new) is Direction.Right:
                # 右包含关系，保留最后一根（调试输出）
                print(array[-1], new)
            else:
                # 其他关系，正常添加
                print(double_relation(array[-1], new))
                array.append(new)

        # 初始化起始时间和索引
        dt = datetime.datetime(2008, 8, 8)
        offset = datetime.timedelta(seconds=seconds)
        index = 0
        
        # 遍历所有价格点生成K线
        for i in range(1, len(points)):
            # 获取当前点和前一点的价格
            if type(points[i]) is dict:
                # 处理字典类型的价格点
                o = int(points[i - 1]["price"])
                c = int(points[i]["price"])
            else:
                # 处理整数类型的价格点
                o = int(points[i - 1])
                c = int(points[i])
                
            # 确定方向、高低点和价差
            direction = Direction.Up if o < c else Direction.Down
            high = max(o, c)
            low = min(o, c)
            d = high - low
            m = d / 5
            
            # 根据方向生成不同类型的K线序列
            if direction == Direction.Up:
                # 上涨序列：先创建基础K线
                nb = Bar.creat_new_bar(dt, low + m, low, direction, 8, index, None)
                append(news, nb)
                dt = dt + offset
                
                # 然后添加连续上涨的4根K线
                for dd in [Direction.NextUp] * 4:
                    nb = Bar.generate(nb, dd, seconds, True)
                    append(news, nb)
                    dt = dt + offset
            else:
                # 下跌序列：先创建基础K线
                nb = Bar.creat_new_bar(dt, high, low + m * 4, direction, 8, index, None)
                append(news, nb)
                dt = dt + offset
                
                # 然后添加连续下跌的4根K线
                for dd in [Direction.NextDown] * 4:
                    nb = Bar.generate(nb, dd, seconds, True)
                    append(news, nb)
                    dt = dt + offset

        # 重置K线索引
        lines = Lines(news)
        lines.reset_line_index()
        return news


class Bitstamp(BaseAnalyzer):
    """
    行情数据分析类
    基于BaseAnalyzer实现的市场数据分析类，支持多种数据源获取和处理历史及实时K线数据
    可对接龙虎VIP、东方财富、QMT等数据源，获取并分析各类金融产品的历史和实时数据
    """
    def __init__(self, pair: str, freq: SupportsInt = 300, ws: WebSocket = None, data_source: str = "QMT"):
        """
        初始化Bitstamp分析器对象
        
        Args:
            pair: 交易品种代码，如股票代码或期货合约代码
            freq: 分析周期，可以是整数秒数或字符串形式周期，默认300秒(5分钟)
            ws: WebSocket连接，用于实时推送分析结果
            data_source: 数据源类型，可选"longhuvip"、"eastmoney"、"qmt"等
        """
        super().__init__(pair, freq, ws)
        self.data_source = data_source  # 数据源
        self.data = []  # 保存所有K线数据
        self.last_update_time = 0  # 最后一次更新时间
        self.zhu_k_push = 0  # 默认为批量推送，后端可被外部赋值

    def init(self, step="30m", start_date=None, end_date=None, size=1000): # 修改参数名和类型提示
        """
        初始化获取K线数据
        根据指定的时间周期、开始日期和结束日期从选定的数据源获取历史K线数据
        
        Args:
            step (str): K线周期 (例如 "1m", "5m", "30m", "1d")
            start_date (Optional[str]): 开始日期 (YYYYMMDD)
            end_date (Optional[str]): 结束日期 (YYYYMMDD)
            size (int): 在没有日期范围时，获取的K线数量 (主要用于非QMT源)
            
        Returns:
            获取到的K线数据列表
        """
        self.freq = step # 保存周期字符串

        print(f"Bitstamp.init 接收到: step={step}, start_date={start_date}, end_date={end_date}, size={size}")

        # QMT 数据源处理
        if self.data_source == "QMT":
            if not start_date or not end_date:
                # 如果 QMT 没有提供日期，则计算默认日期（例如最近一年）
                today = datetime.date.today()
                if not start_date:
                    one_year_ago = today - datetime.timedelta(days=365)
                    start_date = one_year_ago.strftime("%Y%m%d")
                if not end_date:
                    end_date = today.strftime("%Y%m%d")
                print(f"QMT 未提供日期，使用默认: start_date={start_date}, end_date={end_date}")

            print(f"调用 qmt_ohlc: symbol={self.symbol}, period={step}, start_date={start_date}, end_date={end_date}")
            data = self.qmt_ohlc(self.symbol, step, start_date, end_date)

        # 保留其他数据源的逻辑 (如果需要)
        elif self.data_source == "eastmoney":
             # 东方财富可能需要时间戳，如果需要则在这里转换 start_date, end_date
             # start_ts = int(datetime.datetime.strptime(start_date, "%Y%m%d").timestamp()) if start_date else None
             # end_ts = int(datetime.datetime.strptime(end_date, "%Y%m%d").timestamp()) if end_date else None
             # ... 调用 self.ohlc ...
             # 为了简化，我们假设现在只用 QMT，这部分可以注释掉或移除
             raise NotImplementedError("Eastmoney data source not fully adapted in this example")
        elif self.data_source == "longhuvip":
             raise NotImplementedError("Longhuvip data source not fully adapted in this example")
        else: # 旧的 Bitstamp API (可能需要时间戳)
             raise NotImplementedError("Old Bitstamp API source not fully adapted in this example")

        if not data or "data" not in data or "ohlc" not in data["data"]:
            print("错误：未能从数据源获取有效数据。")
            print(f"返回的数据: {data}")
            self.data = [] # 确保 self.data 是列表
            # raise ChanException("获取数据失败") # 或者抛出异常
        else:
            self.data = data["data"]["ohlc"]
            if not self.data:
                 print("警告: 获取到的 ohlc 数据列表为空。")

        # 更新最后更新时间 (对于 QMT 历史数据可能意义不大，但保留逻辑)
        self.last_update_time = int(time.time()) # 使用当前时间戳

        # 按时间排序 (确保 timestamp 字段存在且可比较)
        if self.data:
            try:
                # 假设 timestamp 是字符串形式的 Unix 时间戳
                self.data.sort(key=lambda x: int(x.get("timestamp", 0)))
            except (ValueError, TypeError) as e:
                print(f"警告：排序K线数据时出错: {e}. K线数据可能未排序。")

        # 方案2：分析历史数据时关闭notify，分析完再恢复
        old_show_tv = self.config.ANALYZER_SHON_TV
        if self.zhu_k_push:
            self.config.ANALYZER_SHON_TV = True
        else:
            self.config.ANALYZER_SHON_TV = False
        # 输入到分析引擎
        for bar_data in self.data:
            try:
                # 确保所有值都存在
                ts = bar_data.get("timestamp")
                o = bar_data.get("open")
                h = bar_data.get("high")
                l = bar_data.get("low")
                c = bar_data.get("close")
                v = bar_data.get("volume")

                if None in [ts, o, h, l, c, v]:
                    print(f"警告: 跳过不完整的K线数据: {bar_data}")
                    continue

                # timestamp 需要转换为 datetime 对象传递给 step
                dt_obj = datetime.datetime.fromtimestamp(int(ts))

                self.step(
                    dt_obj, # 传递 datetime 对象
                    o, h, l, c, v,
                )
            except ChanException as e:
                print(f"处理K线数据出错: {e}, 数据: {bar_data}")
            except (ValueError, TypeError) as e:
                 print(f"处理K线数据时类型或值错误: {e}, 数据: {bar_data}")
        self.config.ANALYZER_SHON_TV = old_show_tv
        # 分析完后统一推送一次（可选：可根据你的notify批量推送所有结构）
        if not self.zhu_k_push and self.config.ANALYZER_SHON_TV:
            if hasattr(self, 'notify'):
                self.notify(self, None)  # 这里可根据实际notify批量推送所有结构
        return self.data

    async def update_data(self, step="30m"):
        """
        更新K线数据，获取最新的数据点（伪实时拉取）
        通过异步方式从QMT数据源获取最新K线数据，适用于定时补数据
        Args:
            step: K线周期字符串，如"30m"表示30分钟K线
        Returns:
            bool: 是否成功获取到新数据
        """
        print(f"QMT update_data: step={step}, symbol={self.symbol}")
        if self.data_source != "QMT":
            print("当前数据源不是QMT，未实现其他源的实时更新。")
            return False

        # 1. 获取当前已处理的最后一个K线时间戳
        last_ts = 0
        if self.data and isinstance(self.data, list) and len(self.data) > 0:
            try:
                last_ts = int(self.data[-1]["timestamp"])
            except Exception as e:
                print(f"解析最后K线时间戳失败: {e}")

        # 2. 拉取最新数据（只拉取最近N条，防止数据量过大）
        today = datetime.date.today()
        start_date = (today - datetime.timedelta(days=10)).strftime("%Y%m%d")  # 只查最近10天
        end_date = today.strftime("%Y%m%d")
        data = self.qmt_ohlc(self.symbol, step, start_date, end_date)
        if not data or "data" not in data or "ohlc" not in data["data"]:
            print("QMT update_data: 拉取数据失败")
            return False

        new_ohlc = data["data"]["ohlc"]
        if not new_ohlc:
            print("QMT update_data: 没有新K线")
            return False

        # 3. 只处理比last_ts新的K线
        new_bars = [bar for bar in new_ohlc if int(bar["timestamp"]) > last_ts]
        if not new_bars:
            print("QMT update_data: 没有比last_ts新的K线")
            return False

        # 4. 推送新K线到分析器
        old_show_tv = self.config.ANALYZER_SHON_TV
        if self.zhu_k_push:
            self.config.ANALYZER_SHON_TV = True
        else:
            self.config.ANALYZER_SHON_TV = False
        for bar in new_bars:
            try:
                dt = datetime.datetime.fromtimestamp(int(bar["timestamp"]))
                # print(f"QMT update_data: 推送新K线 {dt}")
                self.step(
                    dt,
                    bar["open"],
                    bar["high"],
                    bar["low"],
                    bar["close"],
                    bar["volume"],
                )
                print(f"QMT update_data: 推送新K线 {dt}")
            except Exception as e:
                print(f"QMT update_data: 推送K线失败: {e}, bar={bar}")
        self.config.ANALYZER_SHON_TV = old_show_tv
        # 分析完后统一推送一次（可选）
        if not self.zhu_k_push and self.config.ANALYZER_SHON_TV:
            if hasattr(self, 'notify'):
                self.notify(self, None)  # 这里可根据实际notify批量推送所有结构
        # 5. 更新self.data
        self.data.extend(new_bars)

        return True

    @staticmethod
    def ohlc(pair: str, step: int, start: int, end: int, length: int = 1000) -> Dict:
        """
        获取东方财富数据源的K线数据
        通过东方财富API获取股票K线数据，支持多种时间周期
        
        Args:
            pair: 股票代码
            step: 时间步长(秒)
            start: 开始时间戳
            end: 结束时间戳
            length: 获取的K线数量上限
            
        Returns:
            包含K线数据的字典
        """
        code = str(pair).split('.')[0]  # 处理带后缀的情况（如.SH/.SZ）
        if code.startswith('6'):
            secid = f"1.{code}"
        else:
            secid = f"0.{code}"
        
        # 设置K线周期 klt 参数
        # 1分钟:1, 5分钟:5, 15分钟:15, 30分钟:30, 60分钟:60, 日K:101, 周K:102, 月K:103
        klt = "5"  # 默认5分钟
        if step == 60:
            klt = "1"
        elif step == 300:
            klt = "5"
        elif step == 900:
            klt = "15"
        elif step == 1800:
            klt = "30"
        elif step == 3600:
            klt = "60"
        elif step == 86400:
            klt = "101"
        
        # 按照用户要求，使用固定的参数值
        begin_param = 0
        end_param = 20500101
        
        # 请求URL
        url = f'https://push2his.eastmoney.com/api/qt/stock/kline/get?fields1=f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13&fields2=f51,f52,f53,f54,f55,f56,f57,f58,f59,f60,f61&beg={begin_param}&end={end_param}&ut=fa5fd1943c7b386f172d6893dbfba10b&rtntype=6&secid={secid}&klt={klt}&fqt=1'
        print(f'请求地址：{url}')
        
        # 发送GET请求
        try:
            response = requests.get(url, timeout=10)
            # 处理JSON响应，提取JSON数据
            json_str = response.text
            print(f"响应内容前100个字符: {json_str[:100]}")
            
            data = json.loads(json_str)
            
            # 检查是否有错误信息
            if data.get('rc') != 0:
                error_msg = data.get('message', '未知错误')
                print(f"API返回错误: {error_msg}")
                return {"data": {"pair": pair, "ohlc": []}}
            
            # 提取code和klines
            if not data.get('data'):
                print(f"API返回数据中没有data字段: {json_str[:200]}")
                return {"data": {"pair": pair, "ohlc": []}}
                
            code = data.get('data', {}).get('code', '')
            klines = data.get('data', {}).get('klines', [])
            
            if not klines:
                print(f"没有获取到K线数据，可能是代码错误或无数据")
                return {"data": {"pair": pair, "ohlc": []}}
                
            # print(klines)
            ohlc_list = []
            
            for kline in klines:
                parts = kline.split(',')
                if len(parts) < 7:  # 至少需要日期+OHLCV等数据
                    continue  # 忽略字段不足的数据
                
                # 解析时间日期并转换为时间戳
                date_str = parts[0]
                try:
                    # 尝试不同的时间格式
                    if len(date_str) > 10:  # 带时分秒
                        dt = datetime.datetime.strptime(date_str, "%Y-%m-%d %H:%M")
                    else:  # 仅日期
                        dt = datetime.datetime.strptime(date_str, "%Y-%m-%d")
                except ValueError as e:
                    print(f"日期解析错误: {date_str}, {e}")
                    continue
                
                timestamp = int(dt.timestamp())
                
                # 构建OHLC条目
                try:
                    ohlc_entry = {
                        "timestamp": str(timestamp),
                        "open": parts[1],
                        "high": parts[3],
                        "low": parts[4],
                        "close": parts[2],
                        "volume": parts[5]
                    }
                    ohlc_list.append(ohlc_entry)
                except IndexError as e:
                    print(f"数据字段解析错误: {parts}, {e}")
                    continue
            
            # 构建返回的数据结构
            result = {
                "data": {
                    "pair": code,
                    "ohlc": ohlc_list
                }
            }
            return result
        except Exception as e:
            print(f"获取东方财富数据出错: {e}")
            traceback.print_exc()
            return {"data": {"pair": pair, "ohlc": []}}

    @staticmethod
    def ohlc_old(pair: str, step: int, start: int, end: int, length: int = 1000) -> Dict:
        """
        获取原始Bitstamp交易所的K线数据
        通过Bitstamp API获取加密货币K线数据(已弃用的方法)
        
        Args:
            pair: 交易对代码，如"btcusd"
            step: 时间步长(秒)
            start: 开始时间戳
            end: 结束时间戳
            length: 获取的K线数量上限
            
        Returns:
            包含K线数据的字典，或None表示获取失败
        """
        proxies = {
            "http": "http://127.0.0.1:7897",
            "https": "http://127.0.0.1:7897",
        }
        s = requests.Session()

        s.headers = {
            "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_2) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/79.0.3945.130 Safari/537.36",
            "content-type": "application/json",
        }
        url = f"https://www.bitstamp.net/api/v2/ohlc/{pair}/?step={step}&limit={length}&start={start}&end={end}"
        print(url)
        resp = s.get(url, timeout=5, proxies=proxies)
        print(resp)
        try:
            js = resp.json()
            return js
        except:
            return None

    def analyze(self):
        """
        分析K线数据，返回分析结果
        将分析器中已处理的缠论元素整理成前端可用格式
        
        Returns:
            Dict: 包含分型、笔、线段和中枢等分析结果的字典
        """
        # 将分析结果整理为前端所需格式
        result = {
            "ohlc": self.data,
            "fenxing": [],
            "bi": [],
            "xianduan": [],
            "zhongku": []
        }
        
        # 分型数据
        for fx in self.fxs:
            result["fenxing"].append({
                "timestamp": str(int(fx.dt.timestamp())),
                "value": fx.speck,
                "type": "ding" if fx.shape == Shape.G else "di"
            })
        
        # 笔数据
        for bi in self.bis:
            result["bi"].append({
                "timestamp": str(int(bi.start.dt.timestamp())),
                "value": bi.start.speck
            })
            
            if bi == self.bis[-1]:  # 最后一笔添加终点
                result["bi"].append({
                    "timestamp": str(int(bi.end.dt.timestamp())),
                    "value": bi.end.speck
                })
        
        # 线段数据
        for xd in self.xds:
            result["xianduan"].append({
                "timestamp": str(int(xd.start.dt.timestamp())),
                "value": xd.start.speck
            })
            
            if xd == self.xds[-1]:  # 最后一段添加终点
                result["xianduan"].append({
                    "timestamp": str(int(xd.end.dt.timestamp())),
                    "value": xd.end.speck
                })
        
        # 中枢数据
        for zs in self.bzss:
            result["zhongku"].append({
                "timestamp": str(int(zs.start.dt.timestamp())),
                "value": zs.zg,  # 中枢上沿
                "zg": zs.zg,
                "zd": zs.zd,  # 中枢下沿
                "end_time": str(int(zs.end.dt.timestamp())),
                "direction": str(zs.direction)
            })
            
        return result

    def qmt_ohlc(self, code: str, period: str, start_date: str, end_date: str):
        """
        使用 StockDataHandler 获取 QMT 数据。

        Args:
            code (str): 股票代码 (例如 "000001")。
            period (str): QMT 周期字符串 (例如 "30m", "1d")。
            start_date (str): 开始日期 (YYYYMMDD)。
            end_date (str): 结束日期 (YYYYMMDD)。

        Returns:
            dict: 包含K线数据的字典。
        """
        print(f"qmt_ohlc: code={code}, period={period}, start_date={start_date}, end_date={end_date}")
        # 股票代码按市场类型加后缀
        stock_code_suffix = ""
        if code.startswith("6"):
            stock_code_suffix = code + ".SH"
        elif code.startswith("0") or code.startswith("3"): # 创业板和科创板也可能是 .SZ
             stock_code_suffix = code + ".SZ"
        # 可以根据需要添加更多市场判断，例如北交所 .BJ
        else:
             # 对于指数或其他代码，可能不需要后缀或有特定后缀
             # 暂时假设如果不是 6, 0, 3 开头，就不加后缀或使用默认
             print(f"警告: 未知的股票代码前缀 '{code[:1]}', 尝试不加后缀。")
             stock_code_suffix = code # 或者根据实际情况处理

        if not stock_code_suffix:
             print(f"错误: 无法确定股票代码 {code} 的市场后缀。")
             return {"data": {"pair": code, "ohlc": []}}

        try:
            # 创建股票数据处理器实例
            # !! 注意：StockDataHandler 构造函数也需要接受字符串周期 !!
            handler = StockDataHandler(
                code_list=[stock_code_suffix],  # 使用带后缀的代码
                period=period,            # 直接传递周期字符串
                start_date=start_date,    # 格式"YYYYMMDD"
                end_date=end_date
            )

            # 获取市场数据并自动下载
            # 确保 StockDataHandler.get_market_data 正确处理周期字符串
            data = handler.get_market_data(need_download=True)
            print(f"qmt_ohlc: 从 handler 获取的数据 data.keys={list(data.keys()) if data else 'None'}")

            # 获取对应代码的数据
            df = data.get(stock_code_suffix) # 使用带后缀的键

            if df is None or df.empty:
                 print(f"警告: 未能获取到代码 {stock_code_suffix} 的数据。")
                 return {"data": {"pair": code, "ohlc": []}}

            # 转换为列表格式
            result = {
                "data": {
                    "pair": code, # 返回原始代码
                    "ohlc": []
                }
            }

            # 检查 DataFrame 列名
            required_cols = {'datetime', 'open', 'high', 'low', 'close', 'volume'}
            if not required_cols.issubset(df.columns):
                print(f"错误: StockDataHandler 返回的 DataFrame 缺少必需的列。需要: {required_cols}, 实际: {df.columns}")
                return {"data": {"pair": code, "ohlc": []}}

            for _, row in df.iterrows():
                try:
                    # 从 datetime 字符串推断时间戳
                    # 假设 datetime 格式为 "YYYY-MM-DD" 或 "YYYY-MM-DD HH:MM:SS"
                    dt_str = row['datetime']
                    if ' ' in dt_str: # 带时间
                        dt_obj = datetime.datetime.strptime(dt_str, "%Y-%m-%d %H:%M:%S")
                    else: # 只有日期
                        dt_obj = datetime.datetime.strptime(dt_str, "%Y-%m-%d")
                    timestamp = int(dt_obj.timestamp())

                    ohlc_entry = {
                        "open": str(row['open']),
                        "high": str(row['high']),
                        "low": str(row['low']),
                        "close": str(row['close']),
                        "volume": str(row['volume']),
                        "timestamp": str(timestamp) # 使用计算出的时间戳
                    }
                    result["data"]["ohlc"].append(ohlc_entry)
                except (ValueError, TypeError) as e:
                    print(f"处理行数据时出错: {e}, 行: {row}")
                except Exception as e:
                     print(f"处理行数据时发生未知错误: {e}, 行: {row}")


            return result
        except ImportError:
             print("错误: 无法导入 StockDataHandler 或其依赖项 (xtquant)。请确保已正确安装。")
             return {"data": {"pair": code, "ohlc": []}}
        except Exception as e:
             print(f"执行 qmt_ohlc 时发生错误: {e}")
             traceback.print_exc()
             return {"data": {"pair": code, "ohlc": []}}

    @staticmethod
    def longhuvip_ohlc(pair: str, step: int, start: int, end: int, length: int = 600) -> Dict:
        """
        获取龙虎VIP数据源的K线数据
        通过龙虎VIP API获取股票K线数据，支持多种时间周期，适用于高级行情分析
        
        Args:
            pair: 股票代码，如"000001"
            step: 时间步长(秒)，对应转换为龙虎VIP的周期类型
            start: 开始时间戳
            end: 结束时间戳
            length: 获取的K线数量上限，默认600条
            
        Returns:
            Dict: 包含K线数据的字典，格式与其他数据源保持一致
        """
        try:
            code = str(pair).split('.')[0]  # 处理带后缀的情况（如.SH/.SZ）
            
            # 设置K线周期参数
            period_type = "60"  # 默认60分钟
            api_function = "GetKLineDay_W14"
            
            if step == 1:  # 1分钟
                period_type = "1"
            elif step == 5:  # 5分钟
                period_type = "5"
            elif step == 15:  # 15分钟
                period_type = "15"
            elif step == 30:  # 30分钟
                period_type = "30"
            elif step == 60:  # 60分钟
                period_type = "60"
            elif step == 1440:  # 日K
                period_type = "d"
            elif step == 604800:  # 周K
                period_type = "w"
            
            # 设置请求头
            headers = {
                'User-Agent': 'lhb/5.18.5 (com.kaipanla.www; build:2; iOS 16.7.2) Alamofire/4.9.1',
                'Accept-Encoding': 'gzip;q=1.0, compress;q=0.5',
                'Content-Type': 'application/x-www-form-urlencoded; charset=utf-8',
                'Accept-Language': 'zh-Hans-CN;q=1.0'
            }
            
            # 设置请求参数
            data = {
                'Index': '0',
                'PhoneOSNew': '2',
                'StockID': code,
                'Token': '',
                'Type': period_type,
                'UserID': '',
                'VerSion': '5.18.0.5',
                'a': api_function,
                'apiv': 'w39',
                'c': 'StockLineData',
                'st': str(length)
            }
            
            # 发送POST请求
            url = 'https://apphis.longhuvip.com/w1/api/index.php'
            print(f'龙湖API请求地址：{url}')
            print(f'龙湖API请求参数：{data}')
            
            response = requests.post(url, headers=headers, data=data, timeout=10)
            
            # 处理响应
            json_str = response.text
            print(f"龙湖API响应内容前100个字符: {json_str[:100]}")
            
            data = json.loads(json_str)
            
            # 检查是否有错误信息
            if data.get('errcode') != "0":
                error_msg = data.get('errinfo', '未知错误')
                print(f"龙湖API返回错误: {error_msg}")
                return {"data": {"pair": pair, "ohlc": []}}
            
            # 检查数据格式
            if 'x' not in data or 'y' not in data:
                print(f"龙湖API返回数据格式不符合预期，缺少必要字段: {data.keys()}")
                return {"data": {"pair": pair, "ohlc": []}}
                
            # 输出数据样例，帮助调试
            x_list = data.get('x', [])
            y_list = data.get('y', [])
            vol_list = data.get('vol', [])
            
            # print(f"龙湖API返回数据: 时间点数量={len(x_list)}, 价格数据数量={len(y_list)}, 成交量数据数量={len(vol_list)}")
            # if len(x_list) > 0:
            #     print(f"时间样例: {x_list[0]}, 类型={type(x_list[0])}")
            # if len(y_list) > 0:
            #     print(f"价格样例: {y_list[0]}, 类型={type(y_list[0])}")
            # if len(vol_list) > 0:
            #     print(f"成交量样例: {vol_list[0]}, 类型={type(vol_list[0])}")
            
            # 生成OHLC列表
            ohlc_list = []
            current_year = datetime.datetime.now().year
            
            # 调试输出前5个时间戳
            if len(x_list) > 5:
                print(f"前5个原始时间戳: {x_list[:5]}")
            
            for i in range(len(x_list)):
                date_str = x_list[i]
                
                # 根据周期类型处理时间格式
                timestamp = 0
                try:
                    if len(date_str) == 8:  # 日期格式 YYYYMMDD
                        year = int(date_str[:4])
                        month = int(date_str[4:6])
                        day = int(date_str[6:8])
                        
                        # 检查年份是否是未来日期，如果是则调整到去年
                        if year > current_year:
                            year = current_year - 1
                            
                        dt = datetime.datetime(year, month, day)
                        timestamp = int(dt.timestamp())
                        
                    elif len(date_str) == 12:  # 分钟线格式 YYYYMMDDHHMM
                        year = int(date_str[:4])
                        month = int(date_str[4:6])
                        day = int(date_str[6:8])
                        hour = int(date_str[8:10])
                        minute = int(date_str[10:12])
                        
                        # 检查年份是否是未来日期，如果是则调整到去年
                        if year > current_year:
                            year = current_year - 1
                            
                        dt = datetime.datetime(year, month, day, hour, minute)
                        timestamp = int(dt.timestamp())
                        
                    else:  # 其他格式，尝试解析
                        try:
                            # 尝试分隔处理，处理可能的逗号分隔格式
                            if ',' in date_str:
                                parts = date_str.split(',')
                                date_part = parts[0]
                                time_part = parts[1] if len(parts) > 1 else "000000"
                                
                                year = int(date_part[:4])
                                # 检查年份是否是未来日期，如果是则调整到去年
                                if year > current_year:
                                    year = current_year - 1
                                    
                                month = int(date_part[4:6])
                                day = int(date_part[6:8])
                                
                                hour = int(time_part[:2])
                                minute = int(time_part[2:4])
                                second = int(time_part[4:6])
                                
                                dt = datetime.datetime(year, month, day, hour, minute, second)
                            else:
                                # 如果是纯数字字符串，尝试按长度解析
                                if date_str.isdigit():
                                    if len(date_str) >= 14:  # YYYYMMDDHHMMSS
                                        year = int(date_str[:4])
                                        # 检查年份是否是未来日期，如果是则调整到去年
                                        if year > current_year:
                                            year = current_year - 1
                                            
                                        month = int(date_str[4:6])
                                        day = int(date_str[6:8])
                                        hour = int(date_str[8:10])
                                        minute = int(date_str[10:12])
                                        second = int(date_str[12:14])
                                        dt = datetime.datetime(year, month, day, hour, minute, second)
                                    else:
                                        # 默认处理为当天日期
                                        print(f"未知日期格式: {date_str}，使用当前日期")
                                        dt = datetime.datetime.now()
                                else:
                                    # 非数字格式，使用日期解析库
                                    print(f"非标准日期格式: {date_str}，使用当前日期")
                                    dt = datetime.datetime.now()
                            
                            timestamp = int(dt.timestamp())
                        except Exception as e:
                            print(f"时间格式解析错误: {date_str}, {e}")
                            # 使用当前时间作为备选
                            timestamp = int(datetime.datetime.now().timestamp())
                except Exception as e:
                    print(f"时间戳解析错误: {date_str}, {e}")
                    timestamp = int(datetime.datetime.now().timestamp())
                
                # 获取OHLC数据
                if i < len(y_list):
                    # 检查y_list元素是否是列表类型
                    y_data = y_list[i]
                    if isinstance(y_data, list) and len(y_data) >= 4:
                        # 根据API文档的描述，y数据数组包含 [开盘价, 收盘价, 最高价, 最低价]
                        try:
                            open_price = float(y_data[0])
                            close_price = float(y_data[1])
                            high_price = float(y_data[2])
                            low_price = float(y_data[3])
                        except (ValueError, TypeError) as e:
                            print(f"价格数据转换错误: {e}, 使用默认值")
                            open_price = close_price = high_price = low_price = 0
                    else:
                        # 如果不是预期的格式，尝试智能解析
                        print(f"OHLC数据格式不符合预期: {y_data}")
                        if isinstance(y_data, list):
                            if len(y_data) == 4:
                                # 假设顺序为：开盘、收盘、最高、最低
                                try:
                                    open_price = float(y_data[0])
                                    close_price = float(y_data[1])
                                    high_price = float(y_data[2])
                                    low_price = float(y_data[3])
                                except (ValueError, TypeError) as e:
                                    print(f"价格数据转换错误: {e}, 使用默认值")
                                    open_price = close_price = high_price = low_price = 0
                            elif len(y_data) > 0:
                                # 使用第一个值作为所有值
                                try:
                                    open_price = close_price = high_price = low_price = float(y_data[0])
                                except (ValueError, TypeError) as e:
                                    print(f"价格数据转换错误: {e}, 使用默认值")
                                    open_price = close_price = high_price = low_price = 0
                            else:
                                # 空列表，使用0作为默认值
                                open_price = close_price = high_price = low_price = 0
                        elif isinstance(y_data, (int, float)):
                            # 如果是单个数值，全部使用该值
                            open_price = close_price = high_price = low_price = float(y_data)
                        else:
                            # 无法解析，使用0
                            open_price = close_price = high_price = low_price = 0
                    
                    volume = vol_list[i] if i < len(vol_list) else 0
                    
                    # 确保volume是浮点数
                    try:
                        volume = float(volume)
                    except (ValueError, TypeError) as e:
                        print(f"成交量数据转换错误: {e}, 使用默认值")
                        volume = 0
                    
                    ohlc_entry = {
                        "timestamp": str(timestamp),
                        "open": str(open_price),
                        "high": str(high_price),
                        "low": str(low_price),
                        "close": str(close_price),
                        "volume": str(volume)
                    }
                    ohlc_list.append(ohlc_entry)
            
            # 按时间戳排序
            ohlc_list.sort(key=lambda x: int(x["timestamp"]))
            
            # 调试输出排序后的前5个时间戳
            if len(ohlc_list) > 5:
                print(f"排序后前5个时间戳: {[datetime.datetime.fromtimestamp(int(x['timestamp'])) for x in ohlc_list[:5]]}")
            
            # 构建返回的数据结构
            result = {
                "data": {
                    "pair": code,
                    "ohlc": ohlc_list
                }
            }
            return result            
        except Exception as e:
            print(f"获取龙湖数据出错: {e}")
            traceback.print_exc()
            return {"data": {"pair": pair, "ohlc": []}}

    def qmt_ohlc(self, code: str, period: str, start_date: str, end_date: str):
        """
        使用QMT数据源获取K线数据
        调用StockDataHandler获取QMT数据，支持股票、ETF、指数等多种金融产品
        
        Args:
            code: 股票代码，如"000001"
            period: QMT周期字符串，如"30m"、"1d"
            start_date: 开始日期，格式为YYYYMMDD
            end_date: 结束日期，格式为YYYYMMDD
            
        Returns:
            Dict: 包含K线数据的字典，统一格式便于后续分析
        """
        print(f"执行qmt_ohlc: code={code}, period={period}, start_date={start_date}, end_date={end_date}")
        # 股票代码按市场类型加后缀
        # 股票代码按市场类型加后缀
        stock_code_suffix = ""
        if code.startswith("sh"):
            stock_code_suffix = code[2:] + ".SH"
        elif code.startswith("sz"):
             stock_code_suffix = code[2:] + ".SZ"
        elif code.startswith("bj"):
            stock_code_suffix = code[2:] + ".BJ"
        # 可以根据需要添加更多市场判断，例如北交所 .BJ
        else:
             # 对于指数或其他代码，可能不需要后缀或有特定后缀
             # 暂时假设如果不是 6, 0, 3 开头，就不加后缀或使用默认
             print(f"警告: 未知的股票代码前缀 '{code[2:]}', 尝试不加后缀。")
             stock_code_suffix = code[2:] # 或者根据实际情况处理

        if not stock_code_suffix:
             print(f"错误: 无法确定股票代码 {code} 的市场后缀。")
             return {"data": {"pair": code, "ohlc": []}}

        try:
            # 创建股票数据处理器实例
            # !! 注意：StockDataHandler 构造函数也需要接受字符串周期 !!
            handler = StockDataHandler(
                code_list=[stock_code_suffix],  # 使用带后缀的代码
                period=period,            # 直接传递周期字符串
                start_date=start_date,    # 格式"YYYYMMDD"
                end_date=end_date
            )

            # 获取市场数据并自动下载
            # 确保 StockDataHandler.get_market_data 正确处理周期字符串
            data = handler.get_market_data(need_download=True)
            print(f"qmt_ohlc: 从 handler 获取的数据 data.keys={list(data.keys()) if data else 'None'}")

            # 获取对应代码的数据
            df = data.get(stock_code_suffix) # 使用带后缀的键
            # print(f"最后一条：{df.iloc[-1]}")
            if df is None or df.empty:
                 print(f"警告: 未能获取到代码 {stock_code_suffix} 的数据。")
                 return {"data": {"pair": code, "ohlc": []}}

            # 转换为列表格式
            result = {
                "data": {
                    "pair": code, # 返回原始代码
                    "ohlc": []
                }
            }

            # 检查 DataFrame 列名
            required_cols = {'datetime', 'open', 'high', 'low', 'close', 'volume'}
            if not required_cols.issubset(df.columns):
                print(f"错误: StockDataHandler 返回的 DataFrame 缺少必需的列。需要: {required_cols}, 实际: {df.columns}")
                return {"data": {"pair": code, "ohlc": []}}

            for _, row in df.iterrows():
                try:
                    # 从 datetime 字符串推断时间戳
                    # 假设 datetime 格式为 "YYYY-MM-DD" 或 "YYYY-MM-DD HH:MM:SS"
                    dt_str = row['datetime']
                    if ' ' in dt_str: # 带时间
                        dt_obj = datetime.datetime.strptime(dt_str, "%Y-%m-%d %H:%M:%S")
                    else: # 只有日期
                        dt_obj = datetime.datetime.strptime(dt_str, "%Y-%m-%d")
                    timestamp = int(dt_obj.timestamp())

                    ohlc_entry = {
                        "open": str(row['open']),
                        "high": str(row['high']),
                        "low": str(row['low']),
                        "close": str(row['close']),
                        "volume": str(row['volume']),
                        "timestamp": str(timestamp) # 使用计算出的时间戳
                    }
                    result["data"]["ohlc"].append(ohlc_entry)
                except (ValueError, TypeError) as e:
                    print(f"处理行数据时出错: {e}, 行: {row}")
                except Exception as e:
                     print(f"处理行数据时发生未知错误: {e}, 行: {row}")


            return result
        except ImportError:
             print("错误: 无法导入 StockDataHandler 或其依赖项 (xtquant)。请确保已正确安装。")
             return {"data": {"pair": code, "ohlc": []}}
        except Exception as e:
             print(f"执行 qmt_ohlc 时发生错误: {e}")
             traceback.print_exc()
             return {"data": {"pair": code, "ohlc": []}}


def gen(symbol: str = "btcusd", limit: int = 500, freq: SupportsInt = Freq.m5, ws: Optional[WebSocket] = None):
    """
    生成随机K线数据的工厂函数
    创建一个能够生成随机方向变化的K线序列的生成器函数
    常用于测试和演示缠论分析功能
    
    Args:
        symbol: 交易品种代码，默认为"btcusd"
        limit: 要生成的K线数量，默认500根
        freq: 时间周期，默认为5分钟
        ws: WebSocket连接对象，用于实时推送分析结果
        
    Returns:
        一个能够生成随机K线数据并进行分析的函数
    """
    def func():
        # 创建Generator实例
        bitstamp = Generator(symbol + "_gen", freq=int(freq), ws=ws)
        bitstamp.config.BI_JUMP = False  # 关闭跳空判定为新K线的功能
        
        # 创建起始K线
        dt = datetime.datetime(2008, 8, 8)  # 设置起始日期
        nb = Bar.creat_new_bar(dt, 10000, 9900, Direction.Up, 8.8, 0)
        bitstamp.push_new_bar(nb)
        
        # 生成指定数量的随机方向K线
        for direction in Direction.generator(int(limit), [Direction.Up, Direction.JumpUp, Direction.NextUp, Direction.Down, Direction.JumpDown, Direction.NextDown]):
            nb = Bar.generate(nb, direction, int(freq))
            bitstamp.push_new_bar(nb)

        # 检查是否生成了带有缺口的线段，如果有则保存数据
        for duan in bitstamp.xds:
            if duan.gap:
                bitstamp.save_nb_file()
                break
        return bitstamp

    return func


def gen2(symbol: str = "btcusd", limit: int = 500, freq: SupportsInt = Freq.m5, ws: Optional[WebSocket] = None):
    """
    根据预定义的价格点生成K线数据的工厂函数
    不同于gen函数的完全随机生成，这个函数基于指定的价格点创建K线
    用于创建特定形态或模式的K线序列，适用于特定场景测试
    
    Args:
        symbol: 交易品种代码，默认为"btcusd"
        limit: 影响生成规模的参数，实际生成量由价格点数量决定
        freq: 时间周期，默认为5分钟
        ws: WebSocket连接对象，用于实时推送分析结果
        
    Returns:
        一个能够生成特定价格点K线数据并进行分析的函数
    """
    def func():
        # 创建Generator实例
        bitstamp = Generator(symbol, freq=int(freq), ws=ws)
        bitstamp.config.BI_JUMP = False  # 关闭跳空判定为新K线的功能
        
        # 定义一系列具体的价格点和时间点
        a = [
            {"price": 11070.490547079706, "time": 1218098700},
            {"price": 11477.076230434637, "time": 1218100200},
            {"price": 10311.530604817166, "time": 1218102000},
            {"price": 10728.958573061562, "time": 1218103200},
            {"price": 9856.15463945964, "time": 1218104700},
            {"price": 10132.632904140995, "time": 1218105900},
            {"price": 9969.998630799022, "time": 1218107700},
            {"price": 10224.792325701446, "time": 1218109200},
            {"price": 9682.168101337797, "time": 1218111900},
            {"price": 9891.448028901257, "time": 1218114000},
        ]
        
        # 使用Generator.generator方法基于价格点生成K线
        for nb in Generator.generator(a, int(freq)):
            bitstamp.push_new_bar(nb)

        # 检查是否生成了带有缺口的线段，如果有则保存数据
        for duan in bitstamp.xds:
            if duan.gap:
                bitstamp.save_nb_file()
                break

    return func


app = FastAPI()
# priority_queue = asyncio.PriorityQueue()
# queue = Observer.queue  # asyncio.Queue()
app.mount(
    "/charting_library",
    StaticFiles(directory="charting_library"),
    name="charting_library",
)
templates = Jinja2Templates(directory="templates")


class ConnectionManager:
    """
    WebSocket连接管理器类
    管理所有客户端的WebSocket连接和相关的分析器实例
    处理连接、断开和消息发送等操作
    """
    def __init__(self):
        """初始化连接管理器，创建连接和分析器的存储字典"""
        self.active_connections: Dict[str, WebSocket] = {}  # 存储活跃的WebSocket连接
        self.analyzers: Dict[str, BaseAnalyzer] = {}  # 存储每个连接对应的分析器实例

    async def connect(self, client_id: str, websocket: WebSocket):
        """
        建立WebSocket连接
        
        Args:
            client_id: 客户端唯一标识
            websocket: WebSocket连接对象
        """
        await websocket.accept()
        self.active_connections[client_id] = websocket

    def disconnect(self, client_id: str):
        """
        断开WebSocket连接
        
        Args:
            client_id: 客户端唯一标识
        """
        if client_id in self.active_connections:
            del self.active_connections[client_id]
        if client_id in self.analyzers:
            del self.analyzers[client_id]

    async def send_message(self, client_id: str, message: dict):
        """
        向指定客户端发送消息
        
        Args:
            client_id: 客户端唯一标识
            message: 要发送的消息字典
        """
        if client_id in self.active_connections:
            await self.active_connections[client_id].send_json(message)

    def get_analyzer(self, client_id: str) -> Optional[BaseAnalyzer]:
        """
        获取指定客户端的分析器实例
        
        Args:
            client_id: 客户端唯一标识
            
        Returns:
            客户端对应的分析器实例，如果不存在则返回None
        """
        # print(f"获取指定客户端的分析器实例: {client_id}")
        return self.analyzers.get(client_id)

    def set_analyzer(self, client_id: str, analyzer: BaseAnalyzer):
        """
        设置客户端的分析器实例
        
        Args:
            client_id: 客户端唯一标识
            analyzer: 分析器实例
        """
        self.analyzers[client_id] = analyzer


# 创建连接管理器实例
manager = ConnectionManager()


@app.websocket("/ws/{client_id}")
async def websocket_endpoint(websocket: WebSocket, client_id: str):
    """
    WebSocket端点处理函数
    处理客户端的WebSocket连接请求和消息交互
    
    Args:
        websocket: WebSocket连接对象
        client_id: 客户端唯一标识
    """
    await manager.connect(client_id, websocket)
    update_task = None
    status_task = None
    
    try:
        while True:
            data = await websocket.receive_text()
            message = json.loads(data)
            print(f"收到WebSocket消息: {message}")

            if message["type"] == "ready":
                # 向客户端发送一个状态消息，表示正在清理和准备获取新数据
                await manager.send_message(client_id, {
                    "type": "status", 
                    "data_source": message.get("data_source", "QMT"),
                    "message": f"正在准备获取 {message['symbol']} 的数据",
                    "timestamp": int(time.time())
                })
                
                # 初始化分析器参数
                symbol = message["symbol"]
                freq_str = message["freq"]  # QMT周期字符串，如"30m", "1d"
                limit = message["limit"]
                data_source = message.get("data_source", "QMT")  # 默认使用QMT数据源
                generator_flag = message["generator"] == "True"  # 是否使用生成器模式

                # 逐K推送参数
                zhu_k_push = int(message.get("zhu_k_push", 1))  # 1为逐K，0为批量
                print(f"逐K推送参数: {zhu_k_push}")

                # 直接从消息中获取日期范围
                start_date_str = message.get("start_date")  # 格式YYYYMMDD
                end_date_str = message.get("end_date")      # 格式YYYYMMDD

                print(f"WebSocket Ready: symbol={symbol}, freq={freq_str}, limit={limit}, generator={generator_flag}, data_source={data_source}, start={start_date_str}, end={end_date_str}, zhu_k_push={zhu_k_push}")

                # 停止现有更新任务
                if update_task and not update_task.done():
                    print("取消更新任务")
                    update_task.cancel()
                
                # 停止状态更新任务
                if status_task and not status_task.done():
                    print("取消状态更新任务")
                    status_task.cancel()
                    
                # 停止现有线程
                if Observer.thread is not None:
                    print("取消现有线程")
                    tmp = Observer.thread
                    Observer.thread = None
                    tmp.join(1)
                    time.sleep(1)

                # 创建新的analyzer实例并运行
                if generator_flag:
                    # 使用生成器模式创建随机K线数据
                    analyzer_func = gen(symbol=symbol, freq=freq_str, limit=limit, ws=websocket)
                else:
                    # 使用真实数据源获取K线数据
                    def analyzer_func():
                        try:
                            print(f"创建分析器: symbol={symbol}, freq={freq_str}, data_source={data_source}")
                            # 创建Bitstamp分析器实例
                            analyzer = Bitstamp(pair=symbol, freq=freq_str, ws=websocket, data_source=data_source)
                            # 设置逐K推送模式
                            analyzer.zhu_k_push = zhu_k_push
                            print(f"初始化分析器: freq={freq_str}, start={start_date_str}, end={end_date_str}, size={limit}, zhu_k_push={zhu_k_push}")
                            # 初始化数据获取
                            analyzer.init(step=freq_str, start_date=start_date_str, end_date=end_date_str, size=int(limit))
                            print(f"分析器初始化完成，获取到 {len(analyzer.data) if hasattr(analyzer, 'data') else 0} 条数据")
                            return analyzer
                        except Exception as e:
                            print(f"创建分析器时出错: {e}")
                            traceback.print_exc()
                            raise

                # 在单独的线程中运行分析器初始化
                def thread_func():
                    try:
                        analyzer = analyzer_func()
                        manager.set_analyzer(client_id, analyzer)
                        print(f"分析器已设置, client_id={client_id}, analyzer={analyzer}")
                        
                        # 分析器创建成功后发送状态消息
                        loop = asyncio.new_event_loop()
                        asyncio.set_event_loop(loop)
                        loop.run_until_complete(
                            manager.send_message(client_id, {
                                "type": "status", 
                                "data_source": data_source,
                                "message": f"成功获取 {symbol} 数据，共 {len(analyzer.data) if hasattr(analyzer, 'data') else 0} 条",
                                "timestamp": int(time.time())
                            })
                        )
                    except Exception as e:
                        print(f"创建分析器时出错: {e}")
                        traceback.print_exc()
                        # 发送错误消息给客户端
                        try:
                            loop = asyncio.new_event_loop()
                            asyncio.set_event_loop(loop)
                            loop.run_until_complete(
                                manager.send_message(client_id, {
                                    "type": "status", 
                                    "data_source": data_source,
                                    "message": f"获取数据出错: {str(e)}",
                                    "timestamp": int(time.time())
                                })
                            )
                        except Exception as e2:
                            print(f"发送错误消息出错: {e2}")

                # 启动分析器线程
                Observer.thread = Thread(target=thread_func)
                Observer.thread.start()
                
                # 等待线程完成，确保分析器已经创建
                time.sleep(3)
                
                # 启动定时更新任务
                async def update_loop():
                    print("启动更新任务")
                    while True:
                        analyzer = manager.get_analyzer(client_id)
                        if not analyzer:
                            # print("更新任务中，analyzer不存在，等待分析器创建...")
                            await asyncio.sleep(2)  # 等待2秒再重试
                            continue
                        # 下面是原有逻辑
                        analyzer_freq_seconds = analyzer.freq
                        update_interval = PERIOD_STRING_TO_SECONDS[analyzer.freq_str]
                        print(f"analyzer_freq_seconds: {analyzer_freq_seconds}")
                        print(f"update_interval: {update_interval}")
                        print(f"更新间隔设置为 {update_interval} 秒 (基于周期 {analyzer.freq_str})")
                        await asyncio.sleep(update_interval)
                        analyzer = manager.get_analyzer(client_id)
                        if analyzer:
                            print("更新数据中。。。")
                            updated = await analyzer.update_data(step=analyzer.freq_str)
                            await manager.send_message(client_id, {
                                "type": "status",
                                "data_source": analyzer.data_source,
                                "message": "数据已更新" if updated else "无新数据",
                                "timestamp": int(time.time())
                            })
                        else:
                            print("Update loop: sleep后analyzer不存在，停止循环。")
                            break

                update_task = asyncio.create_task(update_loop())
                
                # 添加定时状态更新任务
                async def status_loop():
                    print("启动状态更新任务")
                    """定时发送状态更新的异步任务"""
                    while True:
                        # print("状态更新任务中。。。")
                        await asyncio.sleep(15)  # 每5秒发送一次状态更新
                        await manager.send_message(client_id, {
                            "type": "status", 
                            "data_source": data_source,
                            "message": "连接正常",
                            "timestamp": int(time.time())
                        })
                
                status_task = asyncio.create_task(status_loop())

            elif message["type"] == "query_by_index":
                print("收到按索引查询请求")
                # 处理按索引查询特定对象的请求
                analyzer = manager.get_analyzer(client_id)
                if analyzer:
                    data_type = message.get("data_type")
                    print(message.get("index"))
                    index = int(message.get("index").split("-")[-1])

                    try:
                        if data_type == "Bi":
                            # 查询指定索引的笔对象详细信息
                            bi = analyzer.bis[index]
                            data = {
                                "index": bi.index,
                                "start_time": bi.start.dt.timestamp(),
                                "end_time": bi.end.dt.timestamp(),
                                "start_price": bi.start.speck,
                                "end_price": bi.end.speck,
                                "direction": str(bi.direction),
                                "angle": bi.calc_angle(),
                                "speed": bi.calc_speed(),
                                "measure": bi.calc_measure(),
                                "macd": bi.calc_macd(),
                            }
                        elif data_type == "Duan":
                            # 查询指定索引的段对象详细信息
                            duan = analyzer.xds[index]
                            data = {
                                "index": duan.index,
                                "start_time": duan.start.dt.timestamp(),
                                "end_time": duan.end.dt.timestamp(),
                                "start_price": duan.start.speck,
                                "end_price": duan.end.speck,
                                "direction": str(duan.direction),
                                "angle": duan.calc_angle(),
                                "speed": duan.calc_speed(),
                                "measure": duan.calc_measure(),
                                "macd": duan.calc_macd(),
                            }
                        else:
                            raise ValueError(f"不支持的数据类型: {data_type}")

                        # 发送查询结果
                        await manager.send_message(client_id, {"type": "query_result", "success": True, "data_type": data_type, "data": data})

                    except IndexError:
                        # 索引超出范围错误处理
                        await manager.send_message(client_id, {"type": "query_result", "success": False, "message": f"索引 {index} 超出范围"})
                    except Exception as e:
                        # 其他错误处理
                        await manager.send_message(client_id, {"type": "query_result", "success": False, "message": str(e)})

    except WebSocketDisconnect:
        # 处理WebSocket连接断开
        manager.disconnect(client_id)
        # 取消更新任务
        if update_task and not update_task.done():
            print("当客户端断开连接时，取消更新任务")   
            update_task.cancel()
        # 取消状态更新任务
        if status_task and not status_task.done():
            print("当客户端断开连接时，取消状态更新任务")
            status_task.cancel()
        print(f"客户端 {client_id} 断开连接")
    except Exception as e:  # 添加通用异常处理
        # 处理其他异常
        print(f"WebSocket 处理时发生错误: {e}")
        traceback.print_exc()
        manager.disconnect(client_id)
        if update_task and not update_task.done(): update_task.cancel()
        if status_task and not status_task.done(): status_task.cancel()


@app.get("/")
async def main_page(
    request: Request,
    no_generator: str = "network",
    exchange: str = "QMT",
    symbol: str = "sz000001",
    name: str = "平安银行",
    step: int = 30,
    limit: int = 500,
    generator: bool = False,
    start_date: Optional[str] = None,
    end_date: Optional[str] = None,
    zhu_k_push: int = 0,  # 新增，默认1
):
    """
    主页路由处理函数
    渲染主页并传递相关参数给前端
    
    Args:
        request: FastAPI请求对象
        no_generator: 生成器模式参数，默认为"network"
        exchange: 数据源类型，默认为"qmt"
        symbol: 交易品种代码，默认为"000001"
        name: 交易品种名称，默认为"平安银行"
        step: 时间周期(分钟)，默认为30
        limit: 获取的K线数量限制，默认为500
        generator: 是否使用生成器模式，默认为False
        start_date: 开始日期，格式为YYYYMMDD，默认为None
        end_date: 结束日期，格式为YYYYMMDD，默认为None
        
    Returns:
        渲染后的HTML模板响应
    """
    # TradingView分辨率映射
    resolutions = {
        1: "1",
        5: "5",
        15: "15",
        30: "30",  # 保持30代表30分钟
        60: "1H",  # 保持60代表60分钟(虽然QMT用60m, 但前端显示用1H)
        1440: "1D",
        604800: "1W",
        # 可以添加更多QMT支持的周期映射
    }
    
    # QMT实际使用的周期(用于传递给后端)
    qmt_periods = {
        1: "1m",
        5: "5m",
        15: "15m",
        30: "30m",  # QMT使用30m
        60: "60m",  # QMT使用60m
        1440: "1d",
        604800: "1w",
        # 月线等根据QMT API添加
    }

    # 检查TradingView分辨率是否有效
    interval_tv = resolutions.get(step)
    if interval_tv is None:
        # 如果step无效，使用默认值
        step = 30  # 默认30分钟
        interval_tv = resolutions.get(step)

    # 获取QMT使用的周期字符串
    qmt_period_str = qmt_periods.get(step, "30m")  # 默认30m

    # 计算默认日期(如果未提供)
    today = datetime.date.today()
    if start_date is None:
        one_year_ago = today - datetime.timedelta(days=365)
        start_date = one_year_ago.strftime("%Y%m%d")
    if end_date is None:
        end_date = today.strftime("%Y%m%d")

    # 验证日期格式(简单检查)
    try:
        datetime.datetime.strptime(start_date, "%Y%m%d")
        datetime.datetime.strptime(end_date, "%Y%m%d")
    except ValueError:
        # 如果格式错误，回退到默认值
        one_year_ago = today - datetime.timedelta(days=365)
        start_date = one_year_ago.strftime("%Y%m%d")
        end_date = today.strftime("%Y%m%d")
        print(f"警告: 无效的日期格式，已重置为默认日期范围 {start_date} - {end_date}")

    name = get_name(symbol)

    # 返回渲染后的模板
    return templates.TemplateResponse("index.html", {
        "request": request,
        "exchange": exchange,
        "symbol": symbol,
        "name": name,
        "interval": interval_tv,  # 传递给TradingView的分辨率
        "limit": str(limit),
        "step": str(step),  # 原始的step值，可能用于其他逻辑
        "qmt_period": qmt_period_str,  # 传递实际给QMT的周期
        "generator": generator,
        "start_date": start_date,  # YYYYMMDD格式
        "end_date": end_date,       # YYYYMMDD格式
        "zhu_k_push": zhu_k_push,  # 新增
    })

#增加一个股票查询接口
#https://searchadapter.eastmoney.com/api/suggest/get?cb=&input=002478&type=14&token=D43BF722C8E33BDC906FB84D85E326E8&markettype=&mktnum=&jys=&classify=&securitytype=&status=&count=5&_=1747828354772
@app.get("/search")
async def search_page(request: Request, code: str = ""):
    """
    股票查询接口
    提供一个股票查询接口，方便用户查询股票信息
    
    Args:
        request: FastAPI请求对象
        code: 查询的股票代码或名称
        
    Returns:
        JSON格式的股票信息
    """
    if not code:
        return {"status": "error", "message": "请提供查询代码"}
    
    try:
        url = "https://searchadapter.eastmoney.com/api/suggest/get"
        params = {
            "cb": "",
            "input": code,
            "type": "14",
            "token": "D43BF722C8E33BDC906FB84D85E326E8",
            "markettype": "",
            "mktnum": "",
            "jys": "",
            "classify": "",
            "securitytype": "",
            "status": "",
            "count": "5",
            "_": str(int(time.time() * 1000))
        }
        headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
            "Accept": "application/json, text/plain, */*",
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
            "Referer": "https://www.eastmoney.com/",
        }
        
        response = requests.get(url, params=params, headers=headers)
        response.raise_for_status()
        
        # 获取响应文本
        text = response.text
        
        # 处理非标准JSON格式：去掉外层括号
        if text.startswith('(') and text.endswith(')'):
            text = text[1:-1]
        
        # 解析处理后的JSON
        data = json.loads(text)
        
        # 返回查询结果
        return data
    except Exception as e:
        return {"status": "error", "message": f"查询出错: {str(e)}"}

@app.get("/cycle")
async def cycle_page(
    request: Request,
    exchange: str = "QMT",
    symbol: str = "sz000001",
    name: str = "平安银行",
    start_date: Optional[str] = None,
    end_date: Optional[str] = None,
):
    """多周期对比页面"""
    # 处理股票名称
    if symbol.startswith("sh") or symbol.startswith("sz"):
        stock_name = get_name(symbol)
        if stock_name:
            name = stock_name
    
    # 处理日期参数
    current_year = datetime.datetime.now().year
    
    if start_date:
        try:
            # 验证开始日期格式
            assert len(start_date) == 8 and start_date.isdigit()
            year = int(start_date[:4])
            if year > current_year:
                start_date = str(current_year) + start_date[4:]
        except:
            # 默认为一年前
            default_date = datetime.datetime.now() - datetime.timedelta(days=365)
            start_date = default_date.strftime("%Y%m%d")
    else:
        # 默认为一年前
        default_date = datetime.datetime.now() - datetime.timedelta(days=365)
        start_date = default_date.strftime("%Y%m%d")
    
    if end_date:
        try:
            # 验证结束日期格式
            assert len(end_date) == 8 and end_date.isdigit()
            year = int(end_date[:4])
            if year > current_year:
                end_date = str(current_year) + end_date[4:]
        except:
            # 默认为今天
            end_date = datetime.datetime.now().strftime("%Y%m%d")
    else:
        # 默认为今天
        end_date = datetime.datetime.now().strftime("%Y%m%d")
    
    # 确保开始日期不晚于结束日期
    if start_date > end_date:
        start_date, end_date = end_date, start_date
    
    return templates.TemplateResponse(
        "cycle.html",
        {
            "request": request,
            "exchange": exchange,
            "symbol": symbol,
            "name": name,
            "start_date": start_date,
            "end_date": end_date,
        },
    )

if __name__ == "__main__":
    import uvicorn
    uvicorn.run("chan:app", host="localhost", port=8000, reload=True)