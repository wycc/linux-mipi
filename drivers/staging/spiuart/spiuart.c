/*
算法说明:
spiuart_tx_chars里读空缓存，spiuart_send_buf一次性发送



1. /dev/ttySPIx 转发到SPI
2.
*/

#if 1
#include <linux/jiffies.h>
#include <linux/kernel.h>  
#include <linux/delay.h>  
#include <linux/gpio.h>  
#include <linux/init.h>
#include <linux/module.h>
#include <linux/ioctl.h>
#include <linux/fs.h>
#include <linux/device.h>
#include <linux/err.h>
#include <linux/list.h>
#include <linux/errno.h>
#include <linux/mutex.h>
#include <linux/slab.h>
#include <linux/compat.h>
#include <linux/of.h>
#include <linux/of_device.h>
#include <linux/acpi.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/slab.h>
#include <linux/console.h>
#include <linux/platform_device.h>
#include <linux/serial_core.h>
#include <linux/serial_reg.h>
#include <linux/serial.h>
#include <asm/io.h>
#include <asm/irq.h>
#include <linux/spi/spi.h>
#include <linux/tty_flip.h>  
#include <linux/uaccess.h>
#include <linux/of.h>  
#include <linux/of_gpio.h>  
#include <linux/of_platform.h>   
#endif

#define NR_PORTS 2
#define PORT_8250	77
#define SPIUARTMAJOR	252
#define SPIUARTMINORSTART 0
//#define _DEBUG_spiuart
#define UART_BUF_SIZE (64*1024)
#define RDDATA_BUF_SIZE 1024
#define SPEED 1000000
#define GPIO_IRQNUM 32
#define POLL_TIME 0.02
#define FPGA_BUFSIZE 1024


static struct uart_driver spiuart_reg = {
	owner:			THIS_MODULE,
	driver_name:	"spiuart",
	dev_name:		"ttySPI",
	nr:			NR_PORTS,
	cons:			NULL,
};

struct spiuart_data {
	dev_t			devt;
	spinlock_t		spi_lock;
	struct spi_device	*spi;

	/* TX/RX buffers are NULL unless this device is open (users > 0) */
	struct mutex	buf_lock;
	unsigned		users;
	u8			*tx_buffer;
	u8			*rx_buffer;
	u32			speed_hz;
};

static struct uart_port spiuart_ports[NR_PORTS];
static struct spiuart_data *spiuart_l;
static int rxd_int_irq=-1;
static struct task_struct *rxd_task;
static struct task_struct *txd_task;

static void spiuart_tx_chars(struct uart_port *port);

/**********************************************/
/*串口驱动及其实现*/
/**********************************************/
#if 1
//发送fifo是否空
static u_int spiuart_tx_empty(struct uart_port *port)
{
	//uint16_t	ssr;
#ifdef _DEBUG_spiuart
	printk("spiuart_tx_empty\n");
#endif
	/*ssr=spiuart_read_fifo_status();
	ssr &= 1<<(port->line);
	return ssr ? TIOCSER_TEMT : 0;*/
	return TIOCSER_TEMT;
}
//modem控制，也就是CTS，DSR等
//self._port.setDTR(False)  # IO0=HIGH
//self._port.setRTS(True)   # EN=LOW, chip in reset
/*
	This function sets the modem control lines for port described
	by 'port' to the state described by mctrl.  The relevant bits
	of mctrl are:
		- TIOCM_RTS	RTS signal.
		- TIOCM_DTR	DTR signal.
		- TIOCM_OUT1	OUT1 signal.
		- TIOCM_OUT2	OUT2 signal.
		- TIOCM_LOOP	Set the port into loopback mode.
	If the appropriate bit is set, the signal should be driven
	active.  If the bit is clear, the signal should be driven
	inactive.

	Locking: port->lock taken.
	Interrupts: locally disabled.
	This call must not sleep
*/
static void spiuart_set_mctrl(struct uart_port *port, u_int mctrl)
{
	printk("set mctrl: %x", mctrl);
	
	if(mctrl&TIOCM_RTS)	//置一则L，清零H
	{
		printk("clr RTS, io=H");
	}
	else
	{
		printk("set RTS, io=L");
	}
	
	if(mctrl&TIOCM_DTR)
	{
		printk("clr DTR, io=H");
	}
	else
	{
		printk("set DTR, io=L");
	}
	return;
}
//空
/*
	Returns the current state of modem control inputs.  The state
	of the outputs should not be returned, since the core keeps
	track of their state.  The state information should include:
		- TIOCM_CAR	state of DCD signal
		- TIOCM_CTS	state of CTS signal
		- TIOCM_DSR	state of DSR signal
		- TIOCM_RI	state of RI signal
	The bit is set if the signal is currently driven active.  If
	the port does not support CTS, DCD or DSR, the driver should
	indicate that the signal is permanently active.  If RI is
	not available, the signal should not be indicated as active.

	Locking: port->lock taken.
	Interrupts: locally disabled.
	This call must not sleep
*/
static u_int spiuart_get_mctrl(struct uart_port *port)
{
#ifdef _DEBUG_spiuart
	printk("spiuart_get_mctrl\n");
#endif
	return TIOCM_CTS | TIOCM_DSR | TIOCM_CAR;
}
//停止发送
static void spiuart_stop_tx(struct uart_port *port)
{
#ifdef _DEBUG_spiuart
		printk("spiuart_stop_tx\n");
#endif
	//spiuart clean irq by read fifo data, idot.
	//spiuart_read_fifo_data();
}
//发送字符
static void spiuart_start_tx(struct uart_port *port)
{
	//uint8_t ch;
	//uint8_t i;
#ifdef _DEBUG_spiuart
	printk("spiuart_start_tx:%d\n", port->line);
#endif
	spiuart_tx_chars(port);
	return; 
}
//停止接收，空
static void spiuart_stop_rx(struct uart_port *port)
{
#ifdef _DEBUG_spiuart
		printk("spiuart_stop_rx\n");
#endif
}
//空
static void spiuart_enable_ms(struct uart_port *port)
{
#ifdef _DEBUG_spiuart
	printk("spiuart_enable_ms\n");
#endif
}
//空
static void spiuart_break_ctl(struct uart_port *port, int break_state)
{
#ifdef _DEBUG_spiuart
	printk("spiuart_break_ctl\n");
#endif
}
//初始化串口
static int spiuart_startup(struct uart_port *port)
{
	//int retval, i;
	//uint16_t ret;
	//uint8_t gir,sier,sctlr;
	//en
#ifdef _DEBUG_spiuart
	printk("spiuart_start_up\n");
#endif
	//1 1 SHDN=0 PS1/PS0=port->iobase PM=0 PEM=0 TM=0(tx end irq) IR=0 P1=P0=0 B3/B2/B1/B0=0011(9600) 
	//setup port baud 09 for 115200 03 for 9600
	//ret = spiuart_write_reg(port->line, 0x00, 0x09);
	
	

#ifdef _DEBUG_spiuart
	printk("spiuart_startup exit\n");
#endif
	return 0;
}
//关闭串口
static void spiuart_shutdown(struct uart_port *port)
{
	uint8_t gir;
	/*
	 * Free the interrupt
	 */
#ifdef _DEBUG_spiuart
	printk("spiuart_shutdown\n");
#endif
	//free_irq(port->irq, port);
}
//设置终端，空
static void spiuart_set_termios(struct uart_port *port, struct ktermios *termios,
		       struct ktermios *old)
{
unsigned long flags;
unsigned int baud, quot;
unsigned int ulcon, ufcon = 0;
termios->c_cflag &= ~(HUPCL | CMSPAR);
termios->c_cflag |= CLOCAL;
/* 获取用户设置的串口波特率,并计算分频数(串口波特率除数quot) */
baud = uart_get_baud_rate(port, termios, old, 0, 4608000);	//最小波特率，最大波特率
printk("set baud %d",baud);
/* 设置数据字长 */
switch (termios->c_cflag & CSIZE)
{
	case CS5:
	printk("set char len 5");
	break;
	case CS6:
	printk("set char len 6");
	break;
	case CS7:
	printk("set char len 7");
	break;
	case CS8:
	default:
	printk("set char len 8");
	break;
}
// 是否要求设置两个停止位(CSTOPB) 
if (termios->c_cflag & CSTOPB)
{
	printk("set to 2 stop bit");
}
// 是否使用奇偶检验 
if (termios->c_cflag & PARENB)
{
	if (termios->c_cflag & PARODD) //奇校验 
	{
		printk("set odd verify");
	}
	else// 偶校验 
	{
		printk("set to even verify");
	}
}
else// 无校验
{
	printk("set to no veify");
}

//更新串口 FIFO 的超时时限 
//uart_update_timeout(port, termios->c_cflag, baud);

}
//返回串口类型
static const char *spiuart_type(struct uart_port *port)
{
#ifdef _DEBUG_spiuart
	printk("spiuart_type\n");
#endif
	return port->type == PORT_8250 ? "spiuart" : NULL;
}
//释放串口，空
static void spiuart_release_port(struct uart_port *port)
{
#ifdef _DEBUG_spiuart
	printk("spiuart_release_port\n");
#endif
}
//申请串口，空
static int spiuart_request_port(struct uart_port *port)
{
#ifdef _DEBUG_spiuart
	printk("spiuart_request_port\n");
#endif
	return 0;
}
//配置串口
static void spiuart_config_port(struct uart_port *port, int flags)
{
#ifdef _DEBUG_spiuart
	printk("spiuart_config_port\n");
#endif
printk("spiuart_config_port\n");
	if (flags & UART_CONFIG_TYPE && spiuart_request_port(port) == 0)
		port->type = PORT_8250;
}
//校验串口
static int spiuart_verify_port(struct uart_port *port, struct serial_struct *ser)
{
	int ret = 0;
#ifdef _DEBUG_spiuart
	printk("spiuart_verify_port\n");
#endif
	if (ser->type != PORT_UNKNOWN && ser->type != PORT_8250)
		ret = -EINVAL;
	if (port->irq != ser->irq)
		ret = -EINVAL;
	if (ser->io_type != SERIAL_IO_PORT)
		ret = -EINVAL;
	if (port->iobase != ser->port)
		ret = -EINVAL;
	if (ser->hub6 != 0)
		ret = -EINVAL;
	return ret;
}
static struct uart_ops spiuart_ops = {
	tx_empty:	spiuart_tx_empty,
	set_mctrl:	spiuart_set_mctrl,
	get_mctrl:	spiuart_get_mctrl,
	stop_tx:	spiuart_stop_tx,
	start_tx:	spiuart_start_tx,
	stop_rx:	spiuart_stop_rx,
	enable_ms:	spiuart_enable_ms,
	break_ctl:	spiuart_break_ctl,
	startup:	spiuart_startup,
	shutdown:	spiuart_shutdown,
	set_termios:	spiuart_set_termios,
	type:		spiuart_type,
	release_port:	spiuart_release_port,
	request_port:	spiuart_request_port,
	config_port:	spiuart_config_port,
	verify_port:	spiuart_verify_port,
};

#endif
/**********************************************/
/*SPI接口发送串口数据*/
/**********************************************/
static u8 ubuf[NR_PORTS][UART_BUF_SIZE];
static int ubufi[NR_PORTS];
static int ubufj[NR_PORTS];

/*
struct spi_transfer {
	const void	*tx_buf;
	void		*rx_buf;
	unsigned	len;

	dma_addr_t	tx_dma;
	dma_addr_t	rx_dma;
	struct sg_table tx_sg;
	struct sg_table rx_sg;

	unsigned	cs_change:1;
	unsigned	tx_nbits:3;
	unsigned	rx_nbits:3;
#define	SPI_NBITS_SINGLE	0x01 // 1bit transfer 
#define	SPI_NBITS_DUAL		0x02 // 2bits transfer 
#define	SPI_NBITS_QUAD		0x04 // 4bits transfer 
	u8		bits_per_word;
	u16		delay_usecs;
	u32		speed_hz;

	struct list_head transfer_list;
};
*/

__inline uint8_t spiuart_send_char(uint8_t port, uint8_t c)
{
	uint8_t ch;
	uint16_t revdata=0;
	struct spi_transfer st; 
    struct spi_message  msg;  
    spi_message_init( &msg );  

    memset( &st, 0, sizeof(st) );  
	
    st.tx_buf = &c;  
    st.len = 1;  
	st.speed_hz=1000000;
  //填充spi_transfer，将transfer放在队列后面
    spi_message_add_tail( &st, &msg ); 
	spi_sync( spiuart_l->spi, &msg ); 
	return revdata;     //同时读出所有发送FIFO状态
}
void spiuart_init_fillbuf(int port)
{
	ubuf[port][0]=port;
	ubufi[port]=1;
}

__inline spiuart_fillbuf(int port, uint8_t c)
{
	ubuf[port][ubufi[port]]=c;
	ubufi[port]=(ubufi[port]+1)%UART_BUF_SIZE;
	return;
}

void spiuart_send_buf(uint8_t port)
{
	uint8_t ch;
	uint16_t revdata=0;
	struct spi_transfer st; 
    struct spi_message  msg;  
    spi_message_init( &msg );  

    memset( &st, 0, sizeof(st) );  
    st.tx_buf = ubuf[port];  
    st.len = ubufi[port];  
	st.speed_hz=SPEED;
  //填充spi_transfer，将transfer放在队列后面
    spi_message_add_tail( &st, &msg ); 
	spi_sync( spiuart_l->spi, &msg ); 
	return revdata;     //同时读出所有发送FIFO状态
}

/* This just initial proto */
static void spiuart_rx_chars(struct uart_port *port)
{
#ifdef _DEBUG_spiuart
	printk("spiuart_rx_chars\n");
#endif
	return;
}

/* This just initial proto */
static void spiuart_tx_chars(struct uart_port *port)
{
	struct circ_buf* xmit = &port->state->xmit;
	//struct tty_struct* tty = port->state->tty;
	uint16_t txstatus;
	int tmp;
#ifdef _DEBUG_spiuart
	//printk("spiuart_tx_chars\n");
#endif

	if (port->x_char) {
		//向FIFO写入一个数据
		spiuart_send_char(port->line,port->x_char);
		 //printk("TX_CHARS:111111111\n");
		port->icount.tx++;
		port->x_char = 0;
		return;
	}
	if (uart_circ_empty(xmit) || uart_tx_stopped(port)) {  
        return;  
    }  
	//txstatus=spiuart_read_fifo_status();
	tmp=port->icount.tx;

	spiuart_init_fillbuf(port->line);
	while (1){ //(txstatus & (1<<port->line))){//发送FIFO为空则继续发
		//printk("put %d: %c\n", port->icount.tx, xmit->buf[xmit->tail]);
		//printk("TX_CHARS:333333333333\n");
		spiuart_fillbuf(port->line, xmit->buf[xmit->tail]);
		//spiuart_send_char(port->line, xmit->buf[xmit->tail]);
		xmit->tail = (xmit->tail + 1) & (UART_XMIT_SIZE - 1);	//PAGE_SIZE, 4096
		port->icount.tx++;
		
		if (uart_circ_empty(xmit))
			break;
		//if(port->icount.tx-tmp > 512)
		//	break;
	}
	spiuart_send_buf(port->line);
	printk("send %d byte\n",port->icount.tx-tmp);
	
	if (uart_circ_chars_pending(xmit) < WAKEUP_CHARS)	//缓冲器剩余容量小于256
	{
		uart_write_wakeup(port);
	}
	else
	{
		printk("circ full!");
	}
	if (uart_circ_empty(xmit))
	{
		printk("circ empty");
		spiuart_stop_tx(port);
	}

   return;
}


//PB0, num=32
/*
gpio.sh init 32 in
gpio.sh get 32
gpio.sh r 32 
*/
static irqreturn_t spiuartR_int(int irq, void *dev_id)
{
	printk("interrupt handler irq:%d...\n", irq);  
	return IRQ_HANDLED;
}

static irqreturn_t spiuartR_int_thread_fn(int irq, void *dev_id)  
{  
        printk("interrupt handler function:%d...\n", irq);  
        return IRQ_WAKE_THREAD;  
} 
#if 1
#if NR_PORTS<=2
#define INFO_UART {0x7f,0x01,0x02}
#elif NR_PORTS<=4
#define INFO_UART {0x7f,0x01,0x02, 0x03,0x04}
#elif NR_PORTS<=8
#define INFO_UART {0x7f,0x01,0x01,0x02,0x02, 0x03,0x03,0x04,0x04,0x05,0x05,0x06,0x06, 0x07,0x07,0x08,0x08}
#elif NR_PORTS<=16
#define INFO_UART {0x7f,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10}
#elif NR_PORTS<=24
#define INFO_UART {0x7f,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18}
#endif
#endif
//rx不超过256
static const u8 rdinfo_tx[NR_PORTS+1]=INFO_UART;
static u8 rdinfo_rx[NR_PORTS+2]={0};
static u8 rddata_tx[NR_PORTS][RDDATA_BUF_SIZE]={0};
static u8 rddata_rx[NR_PORTS][RDDATA_BUF_SIZE]={0};
static void dump_buf(u8* buf, int len)
{
	int i;
	printk("###00\t01\t02\t03\t04\t05\t06\t07");
	for(i=0; i<len; i++)
	{
		if(i%8==0)printk("\n###");
		printk("%x\t",buf[i]);
	}
	return;
}

//把spi数据转发给串口
static void spiuart_handle_rx(struct uart_port *port, u8* data, int cnt)  
{   
    struct tty_port *tty;  
    unsigned char ch = 0;  
    int i;  
  
    int flag = TTY_NORMAL;  
    if (!port)  
	{
		printk("%s, %d, %s\n", __FILE__, __LINE__, __func__);  
        return;
	}		
    if (!port->state) 
	{	
		printk("%s, %d, %s\n", __FILE__, __LINE__, __func__);  
        return;  
	}
    tty = &(port->state->port);  
    //tty->flags |= TTY_HW_COOK_IN;  
    //tty = port->info->tty;  
    if (!tty)  
	{
		printk("%s, %d, %s\n", __FILE__, __LINE__, __func__);  
        return;  
	}
	for (i = 0; i < cnt; i++) {  
		//用tty_insert_flip_char函数也可以  
		uart_insert_char(port, 0, 0, data[i], flag); 	//使用这个函数正确
		//tty_insert_flip_char(tty, '1',flag);		
	}
	//tty_insert_flip_string(tty, "222", 1);  	//使用此处tty会有未初始化的问题
	//uart_insert_char(port, 0, 0, '1', flag);  
    tty_flip_buffer_push(tty);   
	return;
}  

static int rxd_thread(void *data)
{
	struct spi_transfer st; 
	struct spi_transfer ust[NR_PORTS]; 
	struct spi_message  msg;
	int i,sendport_cnt;
	int cnt[NR_PORTS]={0};
	u16 cnt_l,cnt_h;
	spi_message_init( &msg );  
	memset( &st, 0, sizeof(st) ); 
	while(1){
	   set_current_state(TASK_UNINTERRUPTIBLE);
	   if(kthread_should_stop()) break;
	   if(gpio_get_value(GPIO_IRQNUM)){//有接收中断
			st.tx_buf = rdinfo_tx;
			st.rx_buf = (void*)rdinfo_rx;
			st.len = NR_PORTS+1;  
			st.speed_hz=SPEED;
			//填充spi_transfer，将transfer放在队列后面
			spi_message_add_tail( &st, &msg ); 
			spi_sync( spiuart_l->spi, &msg ); 
			spi_transfer_del(&st);
			//发送完成后读取到fifo 信息
			//dump_buf(st.rx_buf+1, 2*NR_PORTS);
			sendport_cnt = 0;
			for(i=0; i< NR_PORTS; i++)	//逐路读取
			{
				cnt[i] = ((u8*)(st.rx_buf))[i+1];
				//printk("port %d cnt=%d\n",i,cnt[i]);
				if(cnt[i] > 0)
				{
					sendport_cnt++;
					rddata_tx[NR_PORTS][0] = 0x80+i;	//第1字节，读取命令
					rddata_tx[NR_PORTS][1] = (u8)cnt[i];	//第2字节，长度低字节
					rddata_tx[NR_PORTS][2] = 0;	//第3字节，长度高字节
					memset( &(ust[i]), 0, sizeof(st) ); 
					ust[i].tx_buf = (void*)rddata_tx[NR_PORTS];
					ust[i].rx_buf = (void*)rddata_rx[NR_PORTS];
					ust[i].len = cnt[i]+3;
					ust[i].speed_hz=SPEED;
					//spi_message_init( &msg );
					spi_message_add_tail( &ust[i], &msg);
					spi_sync( spiuart_l->spi, &msg ); 
					//printk("read port %d ok\n",i);
					printk("rxd %d byte", cnt[i]);
					//dump_buf(rddata_rx[NR_PORTS], cnt[i]);
					spiuart_handle_rx(&spiuart_ports[i], rddata_rx[NR_PORTS]+3, cnt[i]); 
					spi_transfer_del(&(ust[i]));
										
				}
			}
	   }
	   else{//100ms查看一次
			  schedule_timeout(POLL_TIME*HZ);
	   }
	}
	return 0;
}


/**********************************************/
/*SPI接口相关*/
/**********************************************/

static const struct of_device_id spiuart_dt_ids[] = {
	{ .compatible = "spiuart" },
	{},
};
MODULE_DEVICE_TABLE(of, spiuart_dt_ids);

static int spi_test( struct spiuart_data *spiuart, size_t len, u8 *buf )  
{  
    int w_count = 0, i, page_offset;
    struct spi_transfer st[2]; 
    struct spi_message  msg;  
    spi_message_init( &msg );  

    memset( st, 0, sizeof(st) );  
	
    st[ 0 ].tx_buf = buf;  
    st[ 0 ].len = len;  
	st[0].speed_hz=1000000;
  //填充spi_transfer，将transfer放在队列后面
    spi_message_add_tail( &st[0], &msg );  
  
    st[ 1 ].tx_buf = buf;  
    st[ 1 ].len = len;  
	st[1].speed_hz=1000000;
    spi_message_add_tail( &st[1], &msg );  
  
    spi_sync( spiuart->spi, &msg );   //调用spi_master发送spi_message
    
    return 0;  
} 


static int spiuart_probe(struct spi_device *spi)
{
	struct spiuart_data	*spiuart;
	int			status;
	
#ifdef _DEBUG_spiuart
	printk("%s, %d, %s\n", __FILE__, __LINE__, __func__); 
#endif

	/*
	 * spiuart should never be referenced in DT without a specific
	 * compatible string, it is a Linux implementation thing
	 * rather than a description of the hardware.
	 */
	if (spi->dev.of_node && !of_match_device(spiuart_dt_ids, &spi->dev)) {
		dev_err(&spi->dev, "buggy DT: spiuart listed directly in DT\n");
		WARN_ON(spi->dev.of_node &&
			!of_match_device(spiuart_dt_ids, &spi->dev));
	}

	//spiuart_probe_acpi(spi);

	/* Allocate driver data */
	spiuart = kzalloc(sizeof(*spiuart), GFP_KERNEL);
	if (!spiuart)
		return -ENOMEM;

	/* Initialize the driver data */
	spiuart->spi = spi;
	spin_lock_init(&spiuart->spi_lock);
	mutex_init(&spiuart->buf_lock);
	
	/*
	//无需做设备节点
	struct device *dev;
	spiuart->devt = MKDEV(SPIUART_MAJOR, minor);
	dev = device_create(spiuart_class, &spi->dev, spiuart->devt,
				spiuart, "spiuart%d.%d",
				spi->master->bus_num, spi->chip_select);
	status = PTR_ERR_OR_ZERO(dev);
	*/
	spiuart->speed_hz = 100000;//spi->max_speed_hz;

	status=0;
	if (status == 0)
	{
		spi_set_drvdata(spi, spiuart);
		//spi_test( spiuart, 10, "1234567890"); 
	}
	else
	{
		kfree(spiuart);
	}
	spiuart_l = spiuart;
	//gpio中断
	{
		int i,res,gpio;
		gpio=of_get_named_gpio(spi->dev.of_node,"R-gpio",0);
		if(
		gpio_request(gpio, "rx_int")) printk("rrquest gpio err!\n");	//除了PB0外都能申请。注意申请后要gpio_free()
		gpio_direction_input(gpio); 
		rxd_int_irq=gpio_to_irq(gpio);
		printk("gpio=%d, irq=%d\n",gpio, rxd_int_irq);
		res=request_irq(rxd_int_irq, spiuartR_int, IRQF_TRIGGER_RISING|IRQF_TRIGGER_FALLING, "rint1",  NULL);
		/*res = devm_request_threaded_irq(&(spi->dev), rxd_int_irq, \
			spiuartR_int, spiuartR_int_thread_fn,\
			IRQF_TRIGGER_RISING  |IRQF_ONESHOT,\
			"spiuart", NULL);*/ 	//上升沿,不重入(注意|IRQF_SHARED必须加上最后一个参数，否则报错)
		
		if (res) {
                dev_err(&(spi->dev), "Unable to claim irq %d; error %d\n",rxd_int_irq, res);
                return res;
        }
	}
	//创建内核线程
	kthread_run(rxd_thread, NULL, "rxd_task");
	
	{
		int i;
		for(i=0; i<NR_PORTS;i++)
		{
			ubufi[i]=0;
		}
	}
	return status;
}

static int spiuart_remove(struct spi_device *spi)
{
	struct spiuart_data	*spiuart = spi_get_drvdata(spi);
#ifdef _DEBUG_spiuart
	printk("%s, %d, %s\n", __FILE__, __LINE__, __func__); 
#endif
	/* make sure ops on existing fds can abort cleanly */
	spin_lock_irq(&spiuart->spi_lock);
	spiuart->spi = NULL;
	spin_unlock_irq(&spiuart->spi_lock);

	if (spiuart->users == 0)
		kfree(spiuart);
	
	if(rxd_task){
		kthread_stop(rxd_task);
		rxd_task = NULL;
    }
	if(txd_task){
		kthread_stop(txd_task);
		txd_task = NULL;
    }
	free_irq(rxd_int_irq, NULL);	//释放中断
	gpio_free(32);
	return 0;
}

static struct spi_driver spiuart_spi_driver = {
	.driver = {
		.name =		"spiuart",
		.of_match_table = of_match_ptr(spiuart_dt_ids),
	},
	.probe =	spiuart_probe,
	.remove =	spiuart_remove,
}; 


/**********************************************/
/*初始化相关*/
/**********************************************/

#define PB_INT 0xbc
#define PG_INT 0xc4
static int spiuart_init_ports(void)
{
	static int first = 1;
	int i;
	int retval;
	struct uart_port *port;
#ifdef _DEBUG_spiuart
	printk("%s, %d, %s\n", __FILE__, __LINE__, __func__); 
#endif
	
	if (!first)
		return 0;
	first = 0;
	//setup_spi();
	
	//alloc R irq 
	//request_irq(unsigned int irq, irq_handler_t handler, unsigned long flags, const char *name, void *dev)
	//request_threaded_irq(unsigned int irq, irq_handler_t handler,irq_handler_t thread_fn, unsigned long flags, const char *name, void *dev);
	port = &spiuart_ports[0];
	//retval = request_irq(PB_INT, spiuartR_int, SA_SHIRQ, "spiuart_R", port);
	/*retval = request_threaded_irq(PB_INT, spiuartR_int, spiuartR_int_thread_fn, \
		IRQF_SHARED, "irq_spiuartR", spiuart_ports);  
	if (retval){
		printk("request irq error: %d\n",retval);	
		return retval;
	}*/
	
	for (i = 0; i < NR_PORTS; i++) {
		port = &spiuart_ports[i];
		port->uartclk  = 1843200;
		port->ops      = &spiuart_ops;
		port->fifosize = 64;
		port->type = PORT_8250;

		port->iobase  = (i+1)*1024;
		port->irq     = PB_INT;
		port->iotype  = UPIO_PORT;
		port->flags   = UPF_BOOT_AUTOCONF| UPF_SHARE_IRQ;
		port->line    = i;
		uart_add_one_port (&spiuart_reg, &spiuart_ports[i]);
	}
	
	return 0;
}


//注册SPI设备，UART设备							   
static int __init spiuart_driver_module_init(void)                           
{                                                                          
	int ret=0;                                                           
	printk("spiuart_driver_module_init\r\n");   
	ret = uart_register_driver(&spiuart_reg);	
	if (ret < 0)                                                       
		return ret;                                                
	ret = spiuart_init_ports();
	if (ret < 0)                                                       
		return ret;  
	ret = spi_register_driver(&spiuart_spi_driver);
	if(ret<0)
		return ret;
    return ret;
}                                                                          
									   
static void __exit spiuart_driver_module_exit(void)                          
{         
	int i;
	struct uart_port *port;
	printk("spiuart_driver_module_exit\r\n");
	spi_unregister_driver(&spiuart_spi_driver);                   
	for (i = 0; i < NR_PORTS; i++)
	{
		port = &spiuart_ports[i];
		uart_remove_one_port(&spiuart_reg, &spiuart_ports[i]);
	}
	uart_unregister_driver(&spiuart_reg);
}                                                                          
									   
module_init(spiuart_driver_module_init);  
module_exit(spiuart_driver_module_exit);  
  
MODULE_AUTHOR("zepan <zepanwucai@gmail.com>");  
MODULE_DESCRIPTION("SPI2UART driver");  
MODULE_LICENSE("GPL");  
