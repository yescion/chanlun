from stock_data_handler import StockDataHandler

if __name__ == "__main__":
    # 创建股票数据处理器实例
    handler = StockDataHandler(
        code_list=["000001.SZ"],  # 股票列表
        period="30m",
        start_date="20250430",    # 格式"YYYYMMDD"，开始下载的日期
        end_date="20250505"
    )
    
    # 获取市场数据并自动下载
    data = handler.get_kline_data(need_download=True)
    
    # 保存到CSV文件
    handler.save_to_csv(data)
    
    # 如果需要，还可以订阅行情
    # handler.subscribe_quote()