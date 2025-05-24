from xtquant import xtdata
import time
import pandas as pd
import string
import traceback


class StockDataHandler:
    """
    股票数据处理类，用于下载、订阅和处理股票数据
    """
    
    def __init__(self, code_list=None, period="1m", start_date="", end_date=""):
        """
        初始化股票数据处理器
        
        参数:
            code_list (list): 股票代码列表
            period (str): 数据周期，如"1m", "5m", "1d"等 (应传入标准化格式)
            start_date (str): 开始日期，格式"YYYYMMDD"
            end_date (str): 结束日期，格式"YYYYMMDD"
        """
        self.code_list = code_list if code_list else []
        self.period = period # 直接保存传入的字符串周期
        self.start_date = start_date
        self.end_date = end_date
        self.data = None
    
    def _standardize_period(self, period):
        """
        标准化周期格式
        
        参数:
            period: 输入的周期格式
            
        返回:
            标准化后的周期格式
        """
        # 如果是数字，转换为字符串表示
        if isinstance(period, int):
            if period == 1:
                return "1m"
            elif period == 5:
                return "5m"
            elif period == 15:
                return "15m"
            elif period == 30:
                return "30m"
            elif period == 60:
                return "60m"  # 注意：QMT使用"60m"表示小时线，而不是"1h"
            elif period == 1440:
                return "1d"
            elif period == 10080:
                return "1w"
            elif period == 43200:
                return "1mon"
            else:
                return f"{period}m"
        
        # 已经是字符串，标准化格式
        period_str = str(period)
        return period_str

    def download_data(self, code_list=None, period=None, start_date=None, end_date=None):
        """
        下载股票历史数据
        
        参数:
            code_list (list): 股票代码列表，不指定则使用实例变量
            period (str): 数据周期，不指定则使用实例变量
            start_date (str): 开始日期，不指定则使用实例变量
            end_date (str): 结束日期，不指定则使用实例变量
        """
        code_list = code_list if code_list is not None else self.code_list
        period = period if period is not None else self.period # 直接使用字符串周期
        start_date = start_date if start_date is not None else self.start_date
        end_date = end_date if end_date is not None else self.end_date
        
        # 确保 period 是字符串
        if not isinstance(period, str):
             print(f"警告: download_data 接收到非字符串周期 '{period}', 尝试转换为字符串。")
             period = str(period)
        
        # 确保日期是字符串类型
        if start_date is not None and not isinstance(start_date, str):
            # 如果是时间戳，转换为YYYYMMDD格式
            if isinstance(start_date, int):
                import datetime
                start_date = datetime.datetime.fromtimestamp(start_date).strftime('%Y%m%d')
            else:
                start_date = str(start_date)
                
        if end_date is not None and not isinstance(end_date, str):
            # 如果是时间戳，转换为YYYYMMDD格式
            if isinstance(end_date, int):
                import datetime
                end_date = datetime.datetime.fromtimestamp(end_date).strftime('%Y%m%d')
            else:
                end_date = str(end_date)
        
        n = 1
        num = len(code_list)
        for i in code_list:
            print(f"当前正在下载 {period} {n}/{num}")
            print(f"下载参数: 股票={i}, 周期={period}, 开始日期={start_date}, 结束日期={end_date}")
            try:
                 xtdata.download_history_data(i, period, start_time=start_date, end_time=end_date) # API 使用 start_time, end_time
            except Exception as e:
                 print(f"下载数据时出错: 股票={i}, 周期={period}, 错误: {e}")
                 # 可以选择继续或停止
            n += 1
        print("下载任务结束")
    
    def subscribe_quote(self, code_list=None, period=None):
        """
        订阅股票行情
        
        参数:
            code_list (list): 股票代码列表，不指定则使用实例变量
            period (str): 数据周期，不指定则使用实例变量
        """
        code_list = code_list if code_list is not None else self.code_list
        period = period if period is not None else self.period
        
        for i in code_list:
            xtdata.subscribe_quote(i, period=period)
        time.sleep(1)  # 等待订阅完成
    
    def preprocess_time(self, data=None):
        """
        预处理时间数据
        
        参数:
            data (dict): 股票数据字典，不指定则使用实例变量
            
        返回:
            dict: 处理后的数据
        """
        data = data if data is not None else self.data
        
        if data is None:
            print("警告: preprocess_time 收到空数据。")
            return {} # 返回空字典
        
        processed_data = {}
        for i in data:
            df = data[i]
            if df.empty:
                print(f"警告: 代码 {i} 的 DataFrame 为空，跳过时间处理。")
                processed_data[i] = df # 仍然保留空 DataFrame
                continue

            if 'time' not in df.columns:
                 print(f"错误: 代码 {i} 的 DataFrame 缺少 'time' 列。可用列: {df.columns}")
                 processed_data[i] = df # 返回原始 DataFrame
                 continue

            try:
                 # 假设 time 列是毫秒级时间戳 (xtdata 通常返回这个)
                 df['time'] = pd.to_datetime(df['time'], unit='ms', errors='coerce')
                 df.dropna(subset=['time'], inplace=True) # 删除无法解析的时间戳行

                 if df.empty:
                     print(f"警告: 代码 {i} 在时间戳转换后为空。")
                     processed_data[i] = df
                     continue

                 # 将时间调整为北京时间 (UTC+8) - QMT返回的数据通常已经是本地时间，此步可能不需要或导致错误
                 # 除非确认 xtdata 返回的是 UTC 时间戳
                 df['time'] = df['time'] + pd.Timedelta(hours=8) # 暂时注释掉

                 # 格式化 datetime 列
                 if self.period in ("1d", "1w", "1mon", "1y"):
                     df['datetime'] = df['time'].dt.strftime('%Y-%m-%d')
                 else:
                     df['datetime'] = df['time'].dt.strftime('%Y-%m-%d %H:%M:%S')

                 processed_data[i] = df

            except Exception as e:
                 print(f"处理代码 {i} 的时间时出错: {e}")
                 processed_data[i] = df # 返回未完全处理的 DataFrame

        return processed_data
    
    def get_market_data(self, fields=None, code_list=None, period=None, start_date=None, end_date=None, need_download=False):
        """
        获取股票市场数据
        
        参数:
            fields (list): 需要获取的字段列表
            code_list (list): 股票代码列表，不指定则使用实例变量
            period (str): 数据周期，不指定则使用实例变量
            start_date (str): 开始日期，不指定则使用实例变量
            end_date (str): 结束日期，不指定则使用实例变量
            need_download (bool): 是否需要下载数据
            
        返回:
            dict: 处理后的市场数据
        """
        code_list = code_list if code_list is not None else self.code_list
        period = period if period is not None else self.period # 直接使用字符串周期
        start_date = start_date if start_date is not None else self.start_date
        end_date = end_date if end_date is not None else self.end_date
        fields = fields if fields is not None else ['time', 'open', 'high', 'low', 'close', 'volume']
        
        # 移除标准化调用
        # period = self._standardize_period(period)
        if not isinstance(period, str):
             print(f"警告: get_market_data 接收到非字符串周期 '{period}', 尝试转换为字符串。")
             period = str(period)

        if need_download:
            self.download_data(code_list, period, start_date, end_date)
        
        # 获取历史行情数据
        try:
            print(f"调用 xtdata.get_market_data_ex: fields={fields}, stocks={code_list}, period={period}, start={start_date}, end={end_date}")
            # API 使用 start_time, end_time
            raw_data = xtdata.get_market_data_ex(fields, stock_list=code_list, period=period,
                                             start_time=start_date, end_time=end_date, count=-1, # count=-1 获取范围内所有数据
                                             ) # 尝试填充缺失数据

            if not raw_data:
                 print("警告: xtdata.get_market_data_ex 返回了空数据。")
                 # 返回一个包含空 DataFrame 的字典，以保持结构一致性
                 self.data = {code: pd.DataFrame(columns=fields) for code in code_list}
            else:
                 self.data = raw_data

            # 处理时间数据
            processed_data = self.preprocess_time(self.data) # 使用 self.data

            return processed_data

        except Exception as e:
            print(f"调用 xtdata.get_market_data_ex 时发生错误: {e}")
            traceback.print_exc()
            # 返回空结构以避免后续错误
            return {code: pd.DataFrame(columns=fields) for code in code_list}
    
    def save_to_csv(self, data=None, code_list=None, period=None, start_date=None, end_date=None):
        """
        将数据保存到CSV文件
        
        参数:
            data (dict): 要保存的数据，不指定则使用实例变量
            code_list (list): 股票代码列表，不指定则使用实例变量
            period (str): 数据周期，不指定则使用实例变量
            start_date (str): 开始日期，不指定则使用实例变量
            end_date (str): 结束日期，不指定则使用实例变量
        """
        data = data if data is not None else self.data
        code_list = code_list if code_list is not None else self.code_list
        period = period if period is not None else self.period
        start_date = start_date if start_date is not None else self.start_date
        end_date = end_date if end_date is not None else self.end_date
        
        if data is None:
            raise ValueError("没有可保存的数据，请先获取数据")
        
        for code in code_list:
            if code in data:
                df = data[code]
                filename = f"{code}-{period}-{start_date}-{end_date}.csv"
                df.to_csv(filename, index=True)
                print(f"已保存 {filename}")
            else:
                print(f"警告: 代码 {code} 的数据不存在")


# 用法示例
if __name__ == "__main__":
    # 创建股票数据处理器实例
    handler = StockDataHandler(
        code_list=["159920.SZ"],
        period="1m",
        start_date="20250402",
        end_date="20250405"
    )
    
    # 获取市场数据并自动下载
    data = handler.get_market_data(need_download=True)
    
    # 保存到CSV文件
    handler.save_to_csv() 