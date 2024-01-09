#from SALib.analyze import sobol # для целостного анализа
from SALib import ProblemSpec #для графического анализа

from sklearn.linear_model import LinearRegression
from sklearn.preprocessing import PolynomialFeatures
from sklearn.metrics import r2_score

from sklearn.ensemble import RandomForestRegressor
import seaborn as sns
from scipy.stats import pearsonr




import numpy as np
import json
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
import random
import tkinter as tk
from tkinter import *
from tkinter import ttk
from tkinter import messagebox
from tkinter import simpledialog
from tkinter import filedialog
import csv
import time



from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg


cardict ={} # словарь для записи эксемпляров класса cargo_car по указанному виду ТС
carkey = 0 # идентификатор каждого типа ТС
io = 0
starttime = 0 # переменная локальной временной точки по которой ровняеется цикл, т.е. минимальное время временной точки из всего списка машин. Мастер-цикл в котором используется эта переменная служит временным ограничителем длительности смены или исследумеого промежутка времени
finishTime = 0 # переменная, отвечающая за ограничение исследуемого промежутка времени в мастер-цикле
currentCircle = [] # текущий круг, который уравнивает движение первых автомобилей и тех кто простаивает в очереди (список с минимумом)
minCircle = 0 # текущий минимальый круг на всех машинах в цикле
currentType = 0 # текущий тип автомобиля, который моделируется в цикле
carTime = []
minTime = 0
localTime = [0, 0, 0, 0, 0] # Список из времени начала и окончания погрузки. Третья переменная хранит объект грузящейся машины. Четвертая - тип ТС для carTime. Пятая - номер ТС в типе для carTime
diggerWorkingTime = 0 # рабочее время экскаватора
delaylist = [] # список для последующей записи задержки для каждой машины

CarDelaySum = 0 # суммарная величина простоев машин
CarQSum = 0 # суммарное количество перевезенной работы

FlagOptimize = False # флажок, показывающий начали ли процедуру оптимизации


global Explanation_best_genotype # переменная для хранения лучших генотипов поколения
Explanation_best_genotype = []
global Explanation_best_score # список для хранения лучшего значения целевой функции в поколении
Explanation_best_score = []

class cargo_car:

    def __init__(self, Vfull = 19.52, Vempty = 20, q=240, lempty=2.3, \
                 lfull=2.3, tloadind1=0.13, tloadind2 = 2, \
                 tloadind3 = 0.41, tloadind4 = 1.41, delay = 0.0, kg = 1, rank = 1):
        self.Vfull = Vfull
        self.Vempty =Vempty
        self.q = q
        self.lempty = lempty
        self.lfull = lfull
        self.tloadind1 = tloadind1
        self.tloadind2 = tloadind2
        self.tloadind3 = tloadind3
        self.tloadind4 = tloadind4
        self.delay = delay
        #self.interval = interval
        self.sumQ =0 # суммарное количество перевезенной породы
        self.yQ = [] # список с значениями изменения перевезенной породы
        self.kg = kg # коэффициент грузоподъемности
        self.SumTimeDelay = 0 # суммарное время задержки при простоях в ожидании погрузки
        self.rank = rank # приоритет движения
        self.circle = 0 # круг прохождения в цикле
        self.run = False # едет ли машина
        self.loading = False # на погрузке ли машина
        self.unloading = False # на рагзгрузке ли машина
        self.full = False # заполнен ли кузов машины
        self.waiting = False #  ожидает ли машина
        self.firstTime = True # первый выезд на линию
        # логические знаения говорят о том какое действие происходило перед текущим
        self.L = 0 # Суммарный пробег на маршруте
        self.localTime = 0 # суммарное время на маршруте
        self.Xpos = [] # данные по времени
        self.Ypos = [] # данные по пробегу
        self.localCounter = 0 # локальный счетчик
        self.TransportWork = 0 # транспортная работа в т*км

        self.zeroV = False # наличие нулевой скоости у машины




    # Vfull = 19.52  # скорость в км/ч при полном кузове
    # Vempty = 20  # скорость в км/ч при пустом кузове
    # q = 240  # грузоподъемность в тоннах
    # lempty = 2.3  # длина холостого пробега в км
    # lfull = 2.3  # длина груженого пробега в км
    # tloadind1 = 0.13  # время затрачиваемое под установку на погрузку, мин
    # tloadind2 = 2  # Время погрузки, мин
    # tloadind3 = 0.41  # Время, затрачиваемое установку под разгрузку, мин.
    # tloadind4 = 1.41  # Время разгрузки, мин.

#car1 = cargo_car()

#print(car1.Vfull)
# определяем функцию инициализации класса
def float_or_none(value):
    try:
        float(value)
        return True
    except (ValueError, TypeError):
        return False


def carpam():
    print('hi')
    askForcar(VfullE.get(), VemptyE.get(), qE.get(), lemptyE.get(), lfullE.get(), tloadind1E.get(), tloadind2E.get(), tloadind3E.get(), tloadind4E.get(), countcarE.get())
    countcarE.delete(0,END)

def askForcar(Vfull, Vempty, q, lempty, lfull, tloadind1, tloadind2, tloadind3, tloadind4, countcarE, delay, kg, rank):
    #countcarE - количество ТС в одном типе
    global countcar

    global carkey
    flagc =False # флажок для определения неправильного символа в строке

    delaylist = [] # список с задержками для каждой машины
    mylist = [] # список, куда последовательнос записывается n-е количество одиннаковых экземпляров
    a = countcarE )
    delay = delay.replace(' ','')
    for ins in delay:
        if ins not in '1234567890;.':
            flagc = True
    if flagc == False: #если не встретились неправиьные символы
        delay = delay.split(';')
        if len(delay) == int(a): #проверяем размерность списка и количество указанных ТС в типе
            for ds in delay:
                delaylist.append(float(ds))
        else:

            for co in range(int(a)):
                delaylist.append(float(delay[0])) # записываем для каждой машины задержку выпуска по первому числу

            messagebox.showerror('Error', f'Разная размерность временных меток задержки выпуска и количества ТС.\nЗадержки выпуска уравнены по первому числу')

    else: # встретились неправильные знаки

        for co in range(int(a)):
            delaylist.append(0.0)  # записываем для каждой машины задержку выпуска по умочанию равную 0 минут

        messagebox.showerror('Error', f'Заданный массив задержки выпуска содержит некорректные символы.\n'
                                          f'Задержка выпуска для всех ТС выбранного типа будет равна 0 минут по умолчанию ')


    if a.isdigit():

        carcint = 0
        for key in range(int(a)):
            mylist.append(cargo_car(float(Vfull), float(Vempty), float(q), float(lempty), float(lfull), float(tloadind1), float(tloadind2),
                                    float(tloadind3), float(tloadind4), delaylist[carcint], float(kg), float(rank))) # создание и последующая запись в список нового экземпляра класса
            carcint +=1
        cardict["Type" + str(carkey)] = mylist


    carkey = carkey +1
    countcar['text']=("Количество ТС тип" + str(carkey))


    print(cardict.items())
    print(str(cardict['Type0'][0].Vfull) + ' скорость у первого')
    #if input("Создать еще тип ТС?") == 'y':
    #    askForcar()
    #else:
    #    print("запись ТС закончена")
    #    print(cardict.items())


def mes2():
    logtime1 = time.time() # запись времени для опрееделения производитльности
    global  starttime
    global finishTime
    global workTime
    global cardict



    if cardict == {}:
        messagebox.showerror('Error', 'ТС не были созданы')
    else:
        if starttime >= workTime: # спрашиваем нужно ли произвести новое моделирование
            if messagebox.askyesno('New modeling', f'Моделирование уже было произведено.\nХотите выполнить еще одно моделирование с учетом новых данных?\n'
                                                   f'Все предыдущие данные модели будут утеряны!', icon='warning') == YES:
                # обнуление и приведение ранее записанных машин к дефолтным значениям
                # полное обнуление


                global carTime
                global minTime
                global localTime
                global diggerWorkingTime

                global currentCircle
                global minCircle
                global carkey
                global io
                global currentType
                global delaylist


                carkey = 0  # идентификатор каждого типа ТС
                io = 0
                starttime = 0  # переменная локальной временной точки по которой ровняеется цикл, т.е. минимальное время временной точки из всего списка машин. Мастер-цикл в котором используется эта переменная служит временным ограничителем длительности смены или исследумеого промежутка времени
                finishTime = 0  # переменная, отвечающая за ограничение исследуемого промежутка времени в мастер-цикле
                currentCircle = []  # текущий круг, который уравнивает движение первых автомобилей и тех кто простаивает в очереди (список с минимумом)
                minCircle = 0  # текущий минимальый круг на всех машинах в цикле
                currentType = 0  # текущий тип автомобиля, который моделируется в цикле
                carTime = []
                minTime = 0
                localTime = [0, 0, 0, 0,
                             0]  # Список из времени начала и окончания погрузки. Третья переменная хранит объект грузящейся машины. Четвертая - тип ТС для carTime. Пятая - номер ТС в типе для carTime
                diggerWorkingTime = 0  # рабочее время экскаватора
                delaylist = []  # список для последующей записи задержки для каждой машины

                for delType in cardict.keys():
                    for delOnecar in cardict[delType]:

                        # удаляем параметры каждой машины
                        delOnecar.sumQ = 0  # суммарное количество перевезенной породы
                        delOnecar.yQ = []  # список с значениями изменения перевезенной породы

                        delOnecar.SumTimeDelay = 0  # суммарное время задержки при простоях в ожидании погрузки

                        delOnecar.circle = 0  # круг прохождения в цикле
                        # перезаписываем флажки
                        delOnecar.run = False  # едет ли машина
                        delOnecar.loading = False  # на погрузке ли машина
                        delOnecar.unloading = False  # на рагзгрузке ли машина
                        delOnecar.full = False  # заполнен ли кузов машины
                        delOnecar.waiting = False  # ожидает ли машина
                        delOnecar.firstTime = True  # первый выезд на линию
                        # логические знаения говорят о том какое действие происходило перед текущим
                        delOnecar.L = 0  # Суммарный пробег на маршруте
                        delOnecar.localTime = 0  # суммарное время на маршруте
                        delOnecar.Xpos = []  # данные по времени
                        delOnecar.Ypos = []  # данные по пробегу
                        delOnecar.localCounter = 0  # локальный счетчик
                        delOnecar.TransportWork = 0 # транспортная работа

                #перезапись исследуемого времени
                workTime = simpledialog.askfloat('Work time', 'Укажите рабочее время в минутах', parent=window)
                workTimeaskagain()
                #запуск мастер-цикла
                masterLoop()
                messagebox.showinfo('Simulation', 'Моделирование завершено')
        else:
            masterLoop() # первый запуск мастерцикла после первого нажатия кнопку при откритии программы
            logtime2 = time.time()  # запись времени для опрееделения производитльности
            print('Затрачено времени на моделирование, сек.: ', (logtime2-logtime1))
            messagebox.showinfo('Simulation','Моделирование завершено')

def mes():
    try:

        # проверка на соответствие данных
        if float(VfullE.get()) >= 0 and float(VemptyE.get()) >= 0 and float(qE.get()) >= 0 and float(lemptyE.get()) >= 0 and \
                float(lfullE.get()) >= 0 and float(tloadind1E.get()) >= 0 and float(tloadind2E.get()) >= 0 and \
                float(tloadind3E.get()) >= 0 and float(tloadind4E.get()) >= 0 and float(countcarE.get()) >= 0 and float(
            countcarE.get()) % 1 == 0 \
                and float(kgE.get()) >= 0 and float(rankE.get()) >= 0 and delayE.get() != '' and workTime >= 0:
        # messagebox.showinfo('Создание ТС', '') # срабатывает если можно преобразовать во float

            askForcar(VfullE.get(), VemptyE.get(), qE.get(), lemptyE.get(), lfullE.get(), tloadind1E.get(),
                  tloadind2E.get(), tloadind3E.get(), tloadind4E.get(), countcarE.get(), delayE.get(),
                  kgE.get(), rankE.get())
            countcarE.delete(0, END)
            delayE.delete(0, END)

        else:
            messagebox.askretrycancel('Error', 'Указанные значения не соответствуют требованиям')
            if workTime < 0:
                messagebox.askretrycancel('Error', 'Указанное рабочее время не может быть отрицательным!\nДля перезаписи параметра нажмите кнопку "Стереть"')

        messagebox.showinfo('Vehicle record', 'ТС успешно записаны')
    except Exception:
        messagebox.showerror('Error',
                             "Не все поля заполнены или указыны неверные типы данных")  # выдает ошибку при неправильном заполнении поля




def OptimizeBut():
    global delayCheck1, velocityCheck1, rankCheck1, obl1
    # диалоговое окно по выбору параметров оптимизации
    global windowForOpt
    windowForOpt = tk.Toplevel(window)

    windowForOpt.title('Optimize options')

    frameForOpt = Frame(
        windowForOpt,  # Обязательный параметр, который указывает окно для размещения Frame.
        padx=10,  # Задаём отступ по горизонтали.
        pady=10  # Задаём отступ по вертикали.
    )
    frameForOpt.pack(expand=True)

    obl2 = Label(frameForOpt, text='Оптимизировать по:')
    obl2.grid(row=1, column=1)



    delayCheck1 = tk.BooleanVar()
    velocityCheck1 = tk.BooleanVar()
    rankCheck1 = tk.BooleanVar()

    def get_checkbox_values():
        message = f'Value of checkbox 1: {delayCheck1.get()}\n'
        message += f'Value of checkbox 2: {velocityCheck1.get()}\n'
        message += f'Value of checkbox 3: {rankCheck1.get()}\n'
        message += f'Value of Radio: {varRadbut.get()}\n'
        messagebox.showinfo('Checkbox values', message)


    delayCheck = Checkbutton(frameForOpt, text='задержке выпуска', variable = delayCheck1, onvalue=1, offvalue=0,)
    delayCheck.grid(row=2, column=1, sticky="w")

    velocityCheck = Checkbutton(frameForOpt, text='скорости', variable = velocityCheck1)
    velocityCheck.grid(row=3, column=1, sticky="w")

    rankCheck = Checkbutton(frameForOpt, text='приоритету', variable = rankCheck1)
    rankCheck.grid(row=4, column=1, sticky="w")

    obl1 = Label(frameForOpt, text = 'Целевая функция оптимизируется по:')
    obl1.grid(row=1, column=2)



    global varRadbut
    varRadbut = tk.IntVar()
    varRadbut.set(1)


    delaySumCarCheck = Radiobutton(frameForOpt, text='вывезенной породе, т', variable =varRadbut, value = 1)
    delaySumCarCheck.grid(row=2, column=2, sticky="w")

    delaySumDiggerCheck = Radiobutton(frameForOpt, text='простоям экскаватора, мин.', variable =varRadbut, value = 2)
    delaySumDiggerCheck.grid(row=3, column=2, sticky="w")

    SubQCheck = Radiobutton(frameForOpt, text='простоям автомобилей, мин.', variable =varRadbut, value = 3)
    SubQCheck.grid(row=4, column=2, sticky="w")

    TransportWorkCheck =Radiobutton(frameForOpt, text='транспортной работе, т*км', variable =varRadbut, value = 4)
    TransportWorkCheck.grid(row=5, column=2, sticky="w")

    delaySumCarCheck.select() # нужно выбрать какую-то одну Radiobutton

    frameForOpt2 = Frame(
        windowForOpt,
        padx=10,
        pady=10
    )
    frameForOpt2.pack(expand=True)

    global MyPopulationEnter, MyGenerationEnter, MyMutationRate, Mydeviation

    MyPopulation = Label(frameForOpt2, text='Размер популяции')
    MyPopulation.grid(row=1, column=1, sticky="w")
    MyPopulationEnter = Entry(frameForOpt2)
    MyPopulationEnter.grid(row=1, column=2, sticky="w")

    MyGeneration = Label(frameForOpt2, text='Количество поколений')
    MyGeneration.grid(row=2, column=1, sticky="w")
    MyGenerationEnter = Entry(frameForOpt2)
    MyGenerationEnter.grid(row=2, column=2, sticky="w")

    MyMutationRate = Label(frameForOpt2, text='Порог мутации, %')
    MyMutationRate.grid(row=3, column=1, sticky="w")
    MyMutationRate = Entry(frameForOpt2)
    MyMutationRate.grid(row=3, column=2, sticky="w")

    Mydeviation = Label(frameForOpt2, text='Девиация') # Уровень отклонения при мутации
    Mydeviation.grid(row=4, column=1, sticky="w")
    Mydeviation = Entry(frameForOpt2)
    Mydeviation.grid(row=4, column=2, sticky="w")

    butOptimizeStart = Button(frameForOpt2, text = 'Начать оптимизацию', command = InformationCkech)
    butOptimizeStart.grid(row=5,column=2)

    global GA_explanation
    GA_explanation = tk.BooleanVar()
    GA_ex = Checkbutton(frameForOpt2, text='Объяснить ГА', variable=GA_explanation)
    GA_ex.grid(row=5, column=1)







def InformationCkech():
    global delayCheck1, velocityCheck, rankCheck1, windowForOpt, delayCheckk_value
    global MyPopulationEnter, MyGenerationEnter, MyMutationRate, Mydeviation
    if (delayCheck1.get() !=0 or velocityCheck1.get() !=0 or rankCheck1.get() !=0) and (MyPopulationEnter.get() !='' and
    MyGenerationEnter.get() != '' and MyMutationRate.get() != '' and Mydeviation.get() != ''):

        try:
            global PopulationVal, GenerationVal, MutationRateVal, DeviationVal
            PopulationVal = float(MyPopulationEnter.get())
            GenerationVal = float(MyGenerationEnter.get())
            MutationRateVal = float(MyMutationRate.get())
            DeviationVal = float(Mydeviation.get())
        except:
            messagebox.showerror('Optimize error', f'Параметры заданы неправильно!\nНельзя оптимизировать')
            return
        if (PopulationVal >= 1 and PopulationVal % 1 == 0 and
            GenerationVal >=1 and PopulationVal % 1 == 0 and
            MutationRateVal >= 0 and MutationRateVal <=1 and # MutationRateVal отвечает за процент, поэтому от 0 до 1
            DeviationVal > 0): # эо значение может быть любым больше 0

            PopulationVal = int(MyPopulationEnter.get())
            GenerationVal = int(MyGenerationEnter.get())



            windowForOpt.destroy()

            GAfunction()  # запускаем функцию с генетическим алгоритмом
        else:
            messagebox.showerror('Optimize error', f'Параметры заданы неправильно!\nНельзя оптимизировать')




    else:
        messagebox.showerror('Optimize error', f'Параметры не заданы!\nНельзя оптимизировать')




def OptimizeFunction(MyDelay, MyVfull, MyVempty, Myrank, FinishRewrite = False): # функция оценки, которую мы будет оптимизировать
    #порядок передачи аргрументов в соответствии с вызовом

    global delayCheck1, velocityCheck1, rankCheck1
    global varRadbut

    # обнуление и приведение ранее записанных машин к дефолтным значениям
    # полное обнуление
    global starttime
    global finishTime
    global workTime
    global cardict


    global carTime
    global minTime
    global localTime
    global diggerWorkingTime

    global currentCircle
    global minCircle
    global carkey
    global io
    global currentType
    global delaylist

    global CarDelaySum
    global CarQSum



    CarDelaySum = 0  # суммарная величина простоев машин
    CarQSum = 0  # суммарное количество перевезенной работы

    carkey = 0  # идентификатор каждого типа ТС
    io = 0
    starttime = 0  # переменная локальной временной точки по которой ровняеется цикл, т.е. минимальное время временной точки из всего списка машин. Мастер-цикл в котором используется эта переменная служит временным ограничителем длительности смены или исследумеого промежутка времени
    finishTime = 0  # переменная, отвечающая за ограничение исследуемого промежутка времени в мастер-цикле
    currentCircle = []  # текущий круг, который уравнивает движение первых автомобилей и тех кто простаивает в очереди (список с минимумом)
    minCircle = 0  # текущий минимальый круг на всех машинах в цикле
    currentType = 0  # текущий тип автомобиля, который моделируется в цикле
    carTime = []
    minTime = 0
    localTime = [0, 0, 0, 0,
                     0]  # Список из времени начала и окончания погрузки. Третья переменная хранит объект грузящейся машины. Четвертая - тип ТС для carTime. Пятая - номер ТС в типе для carTime
    diggerWorkingTime = 0  # рабочее время экскаватора
    delaylist = []  # список для последующей записи задержки для каждой машины
    # window.withdraw() # скрыть видимость окна
    # cardict = {}  # словарь для записи эксемпляров класса cargo_car по указанному виду ТС
    # cardict содержит данные о записанных экземпляров класса (машины разных типов). Нужно привести к начальым значениям их параметры
    for delType in cardict.keys():
        for delOnecar in cardict[delType]:
            # удаляем параметры каждой машины
            delOnecar.sumQ = 0  # суммарное количество перевезенной породы
            delOnecar.yQ = []  # список с значениями изменения перевезенной породы

            delOnecar.SumTimeDelay = 0  # суммарное время задержки при простоях в ожидании погрузки

            delOnecar.circle = 0  # круг прохождения в цикле
            # перезаписываем флажки
            delOnecar.run = False  # едет ли машина
            delOnecar.loading = False  # на погрузке ли машина
            delOnecar.unloading = False  # на рагзгрузке ли машина
            delOnecar.full = False  # заполнен ли кузов машины
            delOnecar.waiting = False  # ожидает ли машина
            delOnecar.firstTime = True  # первый выезд на линию
            # логические знаения говорят о том какое действие происходило перед текущим
            delOnecar.L = 0  # Суммарный пробег на маршруте
            delOnecar.localTime = 0  # суммарное время на маршруте
            delOnecar.Xpos = []  # данные по времени
            delOnecar.Ypos = []  # данные по пробегу
            delOnecar.localCounter = 0  # локальный счетчик
            delOnecar.TransportWork = 0 # транспортная работа ТС

    #______________


    # счетчик машин
    MycountCar = 0
    for ccc in cardict.keys():
        for cccc in cardict[ccc]:
            if delayCheck1.get() ==True: # выбранные пользователем параметры для варьирования
                cccc.delay = MyDelay[MycountCar]
            if velocityCheck1.get() == True:
                cccc.Vfull = MyVfull[MycountCar]
                cccc.Vempty = MyVempty[MycountCar]
            if rankCheck1.get() == True:
                cccc.rank = Myrank[MycountCar]
            MycountCar +=1 # инкрементируем счетчик


    # начинаем моделирование
    # запуск мастер-цикла
    masterLoop()

    if FinishRewrite == False:
        CarDelaySum1 = 0 # обнуляем переменные
        CarQSum1 = 0
        SumTransportWork1 = 0
        Maxtimevalue1 = 0 # максимальное время работы у машин, чтобы правильно оценить простои экскаватора
        Maxtimevalue2 = 0

        dimCar_delay = [] # соответствующие списки с целевой функцией по каждой машине для объяснимого ГА
        dimCar_TransportWork = []
        dimCar_Q = []
        dimDIg_T = []


        for ccc in cardict.keys():
            for cccc in cardict[ccc]:
                CarDelaySum1 += cccc.SumTimeDelay # суммарная величина простоев машин
                dimCar_delay.append(-cccc.SumTimeDelay)
                CarQSum1 += cccc.sumQ  # суммарное количество перевезенной породы
                dimCar_Q.append(cccc.sumQ)
                SumTransportWork1 += cccc.TransportWork # суммарное количество транспортной работы
                dimCar_TransportWork.append(-cccc.TransportWork)
                Maxtimevalue1  = max(cccc.Xpos) if  cccc.Xpos !=[] else 0 # окончательное время анализа для всех машин
                if Maxtimevalue2 == 0:
                    Maxtimevalue2 = Maxtimevalue1
                elif Maxtimevalue2 < Maxtimevalue1:
                    Maxtimevalue2 = Maxtimevalue1





        if varRadbut.get() == 1:
            return CarQSum1, dimCar_Q # количество вывезенной породы
        elif varRadbut.get() == 2:

            return -(Maxtimevalue2 - diggerWorkingTime), [-(Maxtimevalue2 - diggerWorkingTime) for DigW in range(len(dimCar_Q))] # время простоя экскаватора
        elif varRadbut.get() == 3:
            return -CarDelaySum1, dimCar_delay # простой машин
        else:
            return -SumTransportWork1, dimCar_TransportWork # транспортная работа






def GAfunction():

    global cardict
    global workTime
    global GA_explanation # переменная чекбокс Объяснения генетического алгоритма

    global Explanation_best_genotype # переменная для хранения лучших генотипов поколения
    global Explanation_best_score # список для хранения лучшего значения целевой функции в поколении
    Explanation_best_genotype = []
    Explanation_best_score = []

    if cardict !={}:

        # Генетичекий алгоритм_____________________________________________________________________________________________


        global delayCheck1, velocityCheck1, rankCheck1


        global PopulationVal, GenerationVal, MutationRateVal, DeviationVal


        global FlagOptimize
        FlagOptimize = True



        def checkBound(expr, Lbound, Ubound):
            if Lbound <= expr and expr <= Ubound:
                return expr
            elif expr < Lbound:
                return Lbound
            elif expr > Ubound:
                return Ubound

        # Целевая функция, зависящая от 4 параметров
        # Генерация случайного генотипа
        def generate_genotype(a, b, c, d, bounds, deviation): # a, b, c, d - соответствующие параметры для оптимизации
            genotype = []
            for i in range(len(a)):
                if delayCheck1.get() == True:
                    a_val = random.uniform(checkBound(a[i] - deviation, bounds[0][i][0], bounds[0][i][1]),
                                       checkBound(a[i] + deviation, bounds[0][i][0], bounds[0][i][1]))
                else:
                    a_val = a[i]
                if velocityCheck1.get() == True:
                    b_val = random.uniform(checkBound(b[i] - deviation, bounds[1][i][0], bounds[1][i][1]),
                                       checkBound(b[i] + deviation, bounds[1][i][0], bounds[1][i][1]))
                    c_val = random.uniform(checkBound(c[i] - deviation, bounds[2][i][0], bounds[2][i][1]),
                                       checkBound(c[i] + deviation, bounds[2][i][0], bounds[2][i][1]))
                else:
                    b_val = b[i]
                    c_val = c[i]
                if rankCheck1.get() == True:
                    d_val = random.randint(checkBound(d[i] - deviation, bounds[3][i][0], bounds[3][i][1]),
                                       checkBound(d[i] + deviation, bounds[3][i][0], bounds[3][i][1]))
                else:
                    d_val = d[i]
                genotype.append([a_val, b_val, c_val, d_val])
            return genotype


        def crossover(parent1, parent2):
            crossover_point = random.randint(1, len(parent1) - 1)
            child = parent1[:crossover_point] + parent2[crossover_point:]
            return child




        def mutate(genotype, mutation_rate, deviation, a, b, c, d, bounds):
            for i in range(len(genotype)):
                for j in range(len(genotype[i])):
                    if random.random() < mutation_rate:
                        if j == 0 and delayCheck1.get() ==True:
                            genotype[i][j] = checkBound(
                                genotype[i][j] + random.uniform(a[i] - genotype[i][j] - deviation , a[i] + deviation - genotype[i][j]),
                                bounds[j][i][0], bounds[j][i][1]) # j-й ген i-ой машины
                        elif j == 1 and velocityCheck1.get() ==True:
                            genotype[i][j] = checkBound(
                                genotype[i][j] + random.uniform(b[i] - genotype[i][j] - deviation , b[i] + deviation - genotype[i][j]),
                                bounds[j][i][0], bounds[j][i][1])
                        elif j == 2 and velocityCheck1.get() ==True:
                            genotype[i][j] = checkBound(
                                genotype[i][j] + random.uniform(c[i] - genotype[i][j] - deviation, c[i] + deviation - genotype[i][j]),
                                bounds[j][i][0], bounds[j][i][1])
                        elif j == 3 and rankCheck1.get() ==True:
                            genotype[i][j] = checkBound(
                                genotype[i][j] + random.randint(d[i] - genotype[i][j] - deviation, d[i] + deviation - genotype[i][j]),
                                bounds[j][i][0], bounds[j][i][1])
            return genotype

        # Создание популяции
        def create_population(population_size, deviation, a, b, c, d, bounds):
            population = []
            for i in range(population_size):
                genotype = generate_genotype(a, b, c, d, bounds, deviation)
                population.append(genotype)
            return population

        # Оценка приспособленности генотипа
        def evaluate_population(population, a, b, c, d):
            fitness_scores = []
            fitness_scores_by_car_ALL = []
            for genotype in population:
                fitness_score, fitness_score_by_car_by_genotype = OptimizeFunction([g[0] for g in genotype], [g[1] for g in genotype],
                                                [g[2] for g in genotype], [g[3] for g in genotype])
                fitness_scores.append(fitness_score)
                fitness_scores_by_car_ALL.append(fitness_score_by_car_by_genotype)
            return fitness_scores, fitness_scores_by_car_ALL

        # Выбор лучших генотипов
        def select_parents(population, fitness_scores, num_parents):
            parents = []
            for i in range(num_parents):
                max_index = fitness_scores.index(max(fitness_scores))
                parents.append(population[max_index])
                fitness_scores[
                    max_index] = -99999999
            return parents

        def genetic_algorithm(population_size, num_generations, mutation_rate, deviation, a, b, c, d, bounds):
            global Explanation_best_genotype
            global Explanation_best_score
            progress()
            population = create_population(population_size, deviation, a, b, c, d, bounds)
            for generation in range(num_generations):
                fitness_scores, fitness_score_by_car = evaluate_population(population, a, b, c, d)
                parents = select_parents(population, fitness_scores, 2)
                try:
                    child = crossover(parents[0], parents[1])
                except:
                    child = parents[0]
                mutated_child = mutate(child, mutation_rate, deviation, a, b, c, d, bounds)
                population.append(mutated_child)
                fitness_scores, fitness_score_by_car = evaluate_population(population, a, b, c, d)
                best_genotype_index = fitness_scores.index(max(fitness_scores))
                best_genotype = population[best_genotype_index]  # лучший набор параметров
                if GA_explanation.get() ==True:
                    #
                    Explanation_best_genotype.append(best_genotype) # делаем популяцию, состоящую из лучшего генотипа



                best_scores = max(fitness_scores)  # лучшее значение функции

                progress_update(generation, num_generations-1)

            if GA_explanation.get() == True:

                qw, fitness_score_by_car = evaluate_population(Explanation_best_genotype, a, b, c, d)
                Explanation_best_score = fitness_score_by_car
                redimEx = []
                redimExScore = []
                for row in range(num_generations):
                    for cols in range(len(Explanation_best_genotype[row])):
                        redimEx.append(Explanation_best_genotype[row][cols])
                        redimExScore.append(Explanation_best_score[row][cols])
                Explanation_best_genotype = np.array(redimEx)
                Explanation_best_score = np.array(redimExScore)
                print('Explanation_best_genotype')
                print(Explanation_best_genotype)
                print('Explanation_best_score')
                print(Explanation_best_score)
            return best_genotype, best_scores, population





        # Конец генетического алгоритма_____________________________________________________________________________________


        listDelayCar = []
        listVelocityCarFull = []
        listVelocityCarEmpty = []
        listRankCar = []
        Bounds = [[],[],[],[]]
        Explanation_best_genotype = []
        Explanation_best_score = []

        amount_OF_cars = 0

        for MyType in cardict.keys():

            for MyOnecar in cardict[MyType]:
                listDelayCar.append(MyOnecar.delay) # записываем параметры каждой машыны последовательно в список
                Bounds[0].append((0,workTime)) # записываем в массив задержку машины. Нижняя граница 0 минут
                listVelocityCarFull.append(MyOnecar.Vfull)
                Bounds[1].append((0,MyOnecar.Vfull)) # записываем в массив скорость с верхним ограничением в заданную пользователем
                listVelocityCarEmpty.append(MyOnecar.Vempty)
                Bounds[2].append((0,MyOnecar.Vempty)) # запись в массив скорости при порожнем кузове
                listRankCar.append(MyOnecar.rank)
                Bounds[3].append((0,MyOnecar.rank)) # запись в массив ранга

                amount_OF_cars +=1






        # Старт генетического алгоритма

        # необходимо солюдать последовательность списков варьируемых параметров и последовательности списков с картежами в Bounds, так как это ограниичения для соответствующих элементов
        # параметры генетического алгорита
        POPULATION_size = 5 # размер начально популяии
        NUM_generations = 50 # количество поколений
        MUTATION_rate = 0.5 # пороговое значение мутации. Т.е. вероятность, НИЖЕ которой будут происходить мутации









        best_genotype, best_scores, population = genetic_algorithm(PopulationVal, GenerationVal, MutationRateVal, DeviationVal, listDelayCar, listVelocityCarFull, listVelocityCarEmpty, listRankCar, Bounds)

        FlagOptimize = False

        print("Best genotype: ", best_genotype)
        print('Best result: ', best_scores)
        print('population: ', len(population))


        a = OptimizeFunction([g[0] for g in best_genotype], [g[1] for g in best_genotype],
                            [g[2] for g in best_genotype], [g[3] for g in best_genotype], True)

        if GA_explanation.get() == True:

            # Обучение модели случайного леса
            model = RandomForestRegressor()
            model.fit(Explanation_best_genotype, Explanation_best_score)

            # Получение важности переменных
            feature_importance = model.feature_importances_

            # Вывод результатов
            print("Feature Importance:", feature_importance)




            # тепловая карта

            plt.figure(figsize=(12, 8))
            sns.heatmap([feature_importance], annot=True, cmap='viridis', yticklabels=['Importance'], xticklabels = ['Задержка выпуска', 'Скорость груженого ТС', 'Скорость порожнего ТС', 'Ранг ТС'])
            plt.title('Random forest feature importance')
            plt.show()

            # Построение полинома
            x = range(len(Explanation_best_genotype))
            plt.scatter(x, Explanation_best_score, color='blue', label='Actual_data')
            degree = 5 # степень полинома
            z = np.polyfit(x, Explanation_best_score, degree)
            p = np.poly1d(z)
            yz = p(x)
            SSres = np.sum((Explanation_best_score - yz)**2)
            SStot = np.sum((Explanation_best_score - np.mean(Explanation_best_score))**2)
            if SStot != 0:
                Rdub = 1 - SSres/SStot
            else:
                Rdub = 1

            adjR = 1-((1-Rdub**2)*(len(Explanation_best_score)-1)/(len(Explanation_best_score)-degree))
            if adjR > Rdub:
                adjR = Rdub
            plt.plot(x, p(x),color='red', label=f'tendency, adjR2 = {adjR:.3f}\nR2 = {Rdub:.3f}')
            plt.xlabel('generation * cars')
            plt.ylabel('goal')
            plt.legend()
            plt.show()


            #корреляция через коэффициенты Пирсона

            # Вычисление корреляции для каждого x
            x = np.array([[x1, x2, x3, x4] for x1, x2, x3, x4 in Explanation_best_genotype])
            y = Explanation_best_score
            correlations_and_pvalues = [pearsonr(x[:, i], y.flatten()) for i in range(x.shape[1])]

            correlations_and_pvalues = [(np.nan_to_num(correlation), np.nan_to_num(pvalue)) for correlation, pvalue in correlations_and_pvalues]
            # Визуализация результатов
            plt.figure()
            for i, (correlation, pvalue) in enumerate(correlations_and_pvalues):

                print(f'Correlation between x{i + 1} and y: {correlation:.4f}, p-value: {pvalue:.4f}')
                print(correlation)

                plt.bar(f'x{i+1}', correlation)
                plt.text(f'x{i + 1}', correlation, f'{correlation:.4f}', ha='center', va='bottom')
            plt.xlabel('Input Features')
            plt.ylabel('Pearson Correlation Coefficient')
            plt.title('Correlation between Input Features and Output (y)')
            plt.ylim(-1, 1)
            plt.show()


            print('Результатыт лучших генотипов поколения (размер)')
            print(len(Explanation_best_score))
            print('Лучшие генотипы в каждом поколении (размер)')
            print(len(Explanation_best_genotype))





        messagebox.showinfo('Optimization completed', f'Оптимизация завершена!\nМодель составлена согласно лучшему генотипу')





    else:
        messagebox.showerror('Optimize error', f'ТС не созданы!\nНельзя оптимизировать')






def ShowSuminfo():
    global cardict
    if cardict !={}:
        global diggerWorkingTime, workTime
        CarDelaySum1 = 0
        CarQSum1 = 0
        SumTransportWork1 = 0
        Maxtimevalue1 = 0
        Maxtimevalue2 = 0
        # получаем суммарные показатели простоев, перевезенной породы и времени простоя экскаватора
        for ccc in cardict.keys():
            for cccc in cardict[ccc]:
                CarDelaySum1 += cccc.SumTimeDelay  # суммарная величина простоев машин
                CarQSum1 += cccc.sumQ  # суммарное количество перевезенной породы
                SumTransportWork1 += cccc.TransportWork # суммарная транспортная работа
                Maxtimevalue1 = max(cccc.Xpos) if  cccc.Xpos !=[] else 0 # окончательное время анализа для всех машин
                if Maxtimevalue2 == 0:
                    Maxtimevalue2 = Maxtimevalue1
                elif Maxtimevalue2 < Maxtimevalue1:
                    Maxtimevalue2 = Maxtimevalue1  # перезаписываем минимальное значение времени анализа для машин

        messagebox.showinfo('Summary information', f'Суммарное время простоев ТС {CarDelaySum1}, мин.\n'
                                                   f'Суммарное время простоев экскаватора {Maxtimevalue2 - diggerWorkingTime}, мин.\n'
                                                   f'Суммарный объем перевезенной породы {CarQSum1}, т\n'
                                                f'Суммарная транспортная работа {SumTransportWork1}, т*км')
    else:
        messagebox.showerror('Summary information', 'ТС не записаны')


def saveCSV():
    global cardict

    global diggerWorkingTime
    if cardict =={}:
        messagebox.showerror('Save logs',f'ТС не созданы!\nНельзя записать файл')
    else:
        fn = filedialog.asksaveasfilename() # имя файла

        countAllCar = 0 # счетчик всех машин в типе и всех типов (сумма, так как записываются и машины и их типы)
        counCurrentCar = 0 # счетчик текущей машины и типа (счетчик итераций)
        progress() # создаем окно прогресса
        for ck1 in cardict.values():
            countAllCar += len(ck1)*2  # суммируем все машины по длине списка в каждом типе
        #countAllCar += len(cardict.keys()) # уеличиваем на количество типов


        # записываем заголовок
        with open(fn + '.csv', 'w', newline='') as file: # дополняем файл данным о ТС

            writer = csv.writer(file, dialect='excel', delimiter=';')
            writer.writerow([])
            writer.writerow(['Данные на маршруте'])

            file.close()


        with open(fn + '.csv','a', newline='') as file:
            fieldnames = ['Тип ТС','# ТС','t, мин.','L, км','Q, т'] #заголовки
            writer = csv.DictWriter(file, dialect='excel', delimiter=';', fieldnames=fieldnames)

            # запись информации с маршрута
            for csvtype in cardict.keys():


                c = 0  # счетчик машин в типе
                for csvcar in cardict[csvtype]:

                    writer.writerow({})  # записываем пустую строку в файл
                    writer.writeheader()  # записываем заголовки в файл
                    for timec in range(len(csvcar.Xpos)): # timec - переменная для итерации согласно длине главного списка (времени)
                        writer.writerow({'Тип ТС':int(csvtype.replace('Type','')),'# ТС':c, 't, мин.':csvcar.Xpos[timec], 'L, км':csvcar.Ypos[timec],'Q, т':csvcar.yQ[timec]})
                    c += 1 # счетчик машин в типе
                    counCurrentCar +=1
                    progress_update(counCurrentCar, countAllCar) # вывод прогресса по записи в файл
            file.close()  # закрытие файла

        # запись информации о ТС
        with open(fn + '.csv', 'a', newline='') as file: # дополняем файл данным о ТС

            writer = csv.writer(file, dialect='excel', delimiter=';')



            writer.writerow({})
            writer.writerow({})
            writer.writerow(['Данные о ТС'])


            for csvtype in cardict.keys():
                c = 0
                for csvcar in cardict[csvtype]:

                    writer.writerow([])
                    writer.writerows([['Тип ТС', int(csvtype.replace('Type', ''))],
                                     ['# ТС', c],
                                     ['Скорость при полном кузове, км/ч', csvcar.Vfull],
                                     ['Скорость при пустом кузове, км/ч', csvcar.Vempty],
                                     ['Грузоподъемность, т', csvcar.q],
                                     ['Длина порожней части ездки, км', csvcar.lempty],
                                     ['Длина груженой части ездки, км', csvcar.lfull],
                                     ['Время затрачиваемое под установку на погрузку, мин.', csvcar.tloadind1],
                                     ['Время погрузки, мин.', csvcar.tloadind2],
                                     ['Время, затрачиваемое установку под разгрузку, мин.', csvcar.tloadind3],
                                     ['Время разгрузки, мин.', csvcar.tloadind4],
                                     ['Задержка выпуска на линию, мин.', csvcar.delay],
                                      ['Суммарное количество перевезенной породы, т', csvcar.sumQ],
                                      ['Коэффициент грузоподъемности', csvcar.kg],
                                      ['Суммарное время задержки при простоях в ожидании погрузки, мин.', csvcar.SumTimeDelay],
                                      ['Приоритет движения', csvcar.rank],
                                      ['Суммарный пробег на маршруте, км', csvcar.L]])
                    c += 1
                    counCurrentCar += 1
                    progress_update(counCurrentCar, countAllCar)

            writer.writerow([])
            writer.writerow([])
            writer.writerow(['Время работы экскаватора, мин.', diggerWorkingTime])


            if cardict != {}:
                global workTime
                CarDelaySum1 = 0
                CarQSum1 = 0
                SumTransportWork1 = 0
                Maxtimevalue1 = 0
                Maxtimevalue2 = 0
                # получаем суммарные показатели простоев, перевезенной породы и времени простоя экскаватора
                for ccc in cardict.keys():
                    for cccc in cardict[ccc]:
                        CarDelaySum1 += cccc.SumTimeDelay
                        CarQSum1 += cccc.sumQ
                        SumTransportWork1 += cccc.TransportWork
                        Maxtimevalue1 = max(cccc.Xpos) if  cccc.Xpos !=[] else 0
                        if Maxtimevalue2 == 0:
                            Maxtimevalue2 = Maxtimevalue1
                        elif Maxtimevalue2 < Maxtimevalue1:
                            Maxtimevalue2 = Maxtimevalue1

                writer.writerow(['Суммарное время простоев ТС, мин.', CarDelaySum1])
                writer.writerow(['Суммарное время простоев экскаватора, мин.', Maxtimevalue2 - diggerWorkingTime])
                writer.writerow(['Суммарный объем перевезенной породы, т', CarQSum1])
                writer.writerow(['Суммарная транспортная работа, т*км', SumTransportWork1])
                writer.writerow(['Исследуемый временной  промежуток, мин.', workTime])


            else:
                messagebox.showerror('Summary information', 'ТС не записаны')

            file.close()  # закрытие файла

        if fn != '': # если прервали диалог по выбору файла
            messagebox.showinfo('Save logs', 'Файл успешно сохранен')
        else:
            messagebox.showerror('Save logs', 'Файл не записан')
























def masterLoop():
    global starttime
    global finishTime
    global cardict
    global carTime
    global minTime
    global localTime
    global diggerWorkingTime
    global workTime
    global currentCircle
    global minCircle

    global FlagOptimize

    if FlagOptimize == False:
        progress()
    b=0
    #Обнуление ранее записанных данных по машинам_______

    # Обнуление ранее записанных данных по машинам_______

    for n in cardict.keys():
        carTime.append([]) # создаем вложенные списки по ключам (по количеству типов ТС)
        currentCircle.append([])
        for nn in range(len(cardict[n])):
            carTime[b].append(999999999999) # заполняем ячейку каждой машины большим числом для дальнейшей перезаписи и нахождения миниума по списку
            currentCircle[b].append(999999999999)
        b += 1

    finishTime = workTime # указаываем рабочее время (исследуем промежуток времени), полученный от диалогового окна

    while starttime < finishTime:
        for type1 in cardict.keys():
            excar = 0 # переменная, хранящая объект прошлой машины в цикле в рамках типа
            b = 0  # счетчик элементов внцтри типа
            for car in cardict[type1]:
                if car.Vfull == 0 or car.Vempty == 0 and car.zeroV == False: # zeroV == False - еще не прошло это условие/ выполняется только один раз
                    car.Xpos.append(0)  # если скорость движения нулевая, то мы понимаем что машина не едет, но ее нужно равнять по minTime, но если окажется что у всех нулевая скорость немного прибавляем, чтобы двигать цикл
                    car.Xpos.append(workTime) # сразу   приехал
                    car.L = 0
                    #
                    car.zeroV = True
                    car.Ypos.append(car.L)
                    car.yQ.append(0)
                    b += 1 #
                    continue



                if car.delay > starttime or car.Xpos==[] and car.zeroV == False: # машина ожидает вывода на линию
                    car.Ypos.append(car.L)
                    car.L = car.Ypos[car.localCounter]
                    car.Xpos.append(car.delay)
                    car.yQ.append(car.sumQ)
                    car.localTime = max(car.Xpos)
                    car.localCounter += 1
                    car.waiting = True  # машина ожидает вывода на линию
                    carTime[int(type1.replace('Type',''))][b] = car.localTime
                    b+=1



                    mymin = 0
                    minTime = 0
                    for n in range(len(cardict.keys())):
                        mymin = min(carTime[n])
                        if minTime ==0 and mymin != 999999999999:
                            minTime = mymin
                        elif minTime > mymin:
                            minTime = mymin
                    if FlagOptimize == False:
                        progress_update(minTime, workTime)
                    continue



                elif car.firstTime and car.run == False and car.unloading ==False and car.zeroV == False: # первая поездка после выпуска на линию
                    car.Xpos.append((car.lempty / car.Vempty) * 60 + car.localTime)
                    car.Ypos.append(car.L + car.lempty)
                    car.yQ.append(car.sumQ)
                    car.L = car.Ypos[car.localCounter]
                    car.localTime = max(car.Xpos)

                    car.localCounter += 1
                    car.run = True
                    car.waiting = False
                    car.firstTime = False
                    carTime[int(type1.replace('Type',''))][b] = car.localTime


                    mymin = 0
                    minTime = 0
                    for n in range(len(cardict.keys())):
                        mymin = min(carTime[n])
                        if minTime == 0:
                            minTime = mymin
                        elif minTime > mymin:
                            minTime = mymin

                elif car.run and car.loading == False and car.full == False and (
                            ((car.localTime + car.tloadind1 + car.tloadind2) <= localTime[0]) or (
                            car.localTime >= localTime[1])) and car.zeroV == False:  # погрузка

                    localTime[0] = car.localTime  # запись времени начала погрузки
                    car.Xpos.append(car.tloadind1 + car.tloadind2 + car.localTime)
                    diggerWorkingTime += car.tloadind2
                    car.Ypos.append(car.L + 0)
                    car.L = car.Ypos[car.localCounter]
                    car.localTime = max(car.Xpos)
                    localTime[1] = car.Xpos[car.localCounter]  # запись времени окончания операции погрузки
                    localTime[2] = car # объект машины, который сейчас грузят записываем в список

                    car.localCounter += 1
                    car.run = False
                    car.loading = True
                    car.waiting = True
                    #loadingCheck[n] = 1
                    car.full = True
                    car.sumQ += car.q * car.kg
                    car.yQ.append(car.sumQ) # записываем прирост вывезенной породы
                    car.circle += 1 # инкрементация круга машины при завершении погрузки

                    localTime[3] = int(type1.replace('Type','')) # записываем тип ТС
                    localTime[4] = b # записываем номер ТС в типе
                    carTime[int(type1.replace('Type',''))][b] = car.localTime

                    mymin = 0
                    minTime = 0
                    minCircle = 0
                    for n in range(len(cardict.keys())):
                        mymin = min(carTime[n])
                        myminC = min(currentCircle[n])

                        if minCircle == 0:
                            minCircle = myminC
                        elif minCircle > myminC:
                            minCircle = myminC

                        if minTime == 0:
                            minTime = mymin
                        elif minTime > mymin:
                            minTime = mymin

                elif car.run and car.loading == False and car.full == False and (
                            ((car.localTime + car.tloadind1 + car.tloadind2) > localTime[0]) or (
                            car.localTime < localTime[1])) and car.zeroV == False:  # если кто-то загружается
                    if car.rank > localTime[2].rank and car.zeroV == False: # проверяем есть ли приоритет погрузки
                        #___________ погрузка мошины с более высоким рангом при погрузке друго машины
                        # localTime[0] и localTime[1] не меняются потому что показывают неприкосновенные промежутки времени погрузки автомобиля низкого ранга, так как
                        # автомобиль высокого ранга прерывают погрузку первого и растягивает временной промежуток второго
                        #localTime[0] = car.localTime  # запись времени начала погрузки
                        car.Xpos.append(car.tloadind1 + car.tloadind2 + car.localTime)

                        diggerWorkingTime += car.tloadind2  #- (localTime[2].Xpos[localTime[2].localCounter-1]-car.localTime+(localTime[2].tloadind1 + localTime[2].tloadind2)) # прибавляем время на погрузку машины и отнимаем незаконченное время а погрузку
                        car.Ypos.append(car.L + 0)
                        car.L = car.Ypos[car.localCounter]

                        localTime[2].Xpos[localTime[2].localCounter - 1] = car.localTime
                        # abs(время окончания погрузки машины0 - время окончания погрузки машины1) - это время которого не хватило до окончания погрузки машины низкого ранга
                        localTime[2].yQ[localTime[2].localCounter - 1] = localTime[2].yQ[localTime[2].localCounter - 2] if  (abs(car.localTime - localTime[2].localTime) / localTime[2].tloadind2)>=1 else  localTime[2].q * localTime[2].kg * (1 - (abs(car.localTime - localTime[2].localTime) / localTime[2].tloadind2)) # если время которого не хватило до окончания погрузки превышает время самой погрузки - то погрузки не было и записывается предыдущее значение

                        #localTime[1] = car.Xpos[car.localCounter]  # запись времени окончания операции погрузки
                        localTime[2].Xpos.append(car.Xpos[car.localCounter] + abs(car.localTime - localTime[2].localTime)) # перезаписываем потенциальное окончание погрузки машины с низким рангом после погрузки машины с высоким, которая прервала погрузку
                        localTime[2].Ypos.append(localTime[2].Ypos[localTime[2].localCounter - 1])
                        localTime[2].yQ.append(localTime[2].sumQ)


                        localTime[2].SumTimeDelay += car.tloadind1 + car.tloadind2 # время простоя машины низкого ранга увеличивается на время погрузки машины высокого ранга

                        localTime[1] = localTime[2].Xpos[localTime[2].localCounter] # перезапись localTime[1] как времени окончания погрузки, т.е. время растягивается из-за прерывания машиной высокого ранга

                        car.localTime += abs(car.Xpos[car.localCounter] - car.localTime)
                        localTime[2].localTime += abs(localTime[2].Xpos[localTime[2].localCounter] - localTime[2].localTime) # переопределяем localTime машины низкого ранга, которую прервали

                        # в localTime[2] остается старая машина, потому что она все равно будет грузится последней, т.е. пропуская машину с высоким рангом она все еще остается на погрузке
                        #localTime[2] = car  # объект машины, который сейчас грузят записываем в список

                        localTime[2].localCounter +=1
                        car.localCounter += 1
                        car.run = False
                        car.loading = True
                        car.waiting = True
                        # loadingCheck[n] = 1
                        car.full = True
                        car.sumQ += car.q * car.kg
                        car.yQ.append(car.sumQ)  # записываем прирост вывезенной породы
                        car.circle += 1  # инкрементация круга машины при завершении погрузки

                        carTime[localTime[3]][localTime[4]] = localTime[2].localTime # перезапись localTime для машины низкого ранга, которую прервали

                        carTime[int(type1.replace('Type', ''))][b] = car.localTime

                        mymin = 0
                        minTime = 0
                        minCircle = 0
                        for n in range(len(cardict.keys())):
                            mymin = min(carTime[n])
                            myminC = min(currentCircle[n])

                            if minCircle == 0:
                                minCircle = myminC
                            elif minCircle > myminC:
                                minCircle = myminC

                            if minTime == 0:
                                minTime = mymin
                            elif minTime > mymin:
                                minTime = mymin

                        #______________ конец условия для прерывания___________________

                        # Начало условия для обычного ожидания
                    if car.rank <= localTime[2].rank and car.zeroV == False: # если ранг новой машины равен или меньше грузящейся машины
                        car.Xpos.append(localTime[1])  # ожидаем до окончания операции
                        car.Ypos.append(car.L + 0)
                        car.yQ.append(car.sumQ)
                        car.L = car.Ypos[car.localCounter]
                        car.SumTimeDelay += abs(car.Xpos[car.localCounter - 1] - localTime[1])
                        car.localTime = max(car.Xpos)
                        car.localCounter += 1
                        car.waiting = True
                        carTime[int(type1.replace('Type',''))][b] = car.localTime

                        mymin = 0
                        minTime = 0
                        for n in range(len(cardict.keys())):
                            mymin = min(carTime[n])
                            if minTime == 0:
                                minTime = mymin
                            elif minTime > mymin:
                                minTime = mymin

                elif car.waiting and car.loading and car.full and car.zeroV == False:  # едет на разгрузку
                    car.Xpos.append((car.lfull / car.Vfull) * 60 + car.localTime)
                    car.Ypos.append(car.L + car.lfull)
                    car.yQ.append(car.sumQ)
                    car.L = car.Ypos[car.localCounter]
                    car.localTime = max(car.Xpos)
                    car.TransportWork += car.q * car.kg * car.lfull #запись транспортной работы, т*км

                    car.localCounter += 1
                    car.waiting = False
                    car.loading = False

                    car.run = True
                    carTime[int(type1.replace('Type',''))][b] = car.localTime

                    mymin = 0
                    minTime = 0
                    for n in range(len(cardict.keys())):
                        mymin = min(carTime[n])
                        if minTime == 0:
                            minTime = mymin
                        elif minTime > mymin:
                            minTime = mymin

                elif car.run and car.unloading == False and car.full and car.zeroV == False:  # разгрузка
                    car.Xpos.append(car.tloadind3 + car.tloadind4 + car.localTime)
                    car.Ypos.append(car.L + 0)
                    car.yQ.append(car.sumQ)
                    car.L = car.Ypos[car.localCounter]
                    car.localTime = max(car.Xpos)

                    car.localCounter += 1
                    car.run = False
                    car.unloading = True
                    car.full = False
                    carTime[int(type1.replace('Type',''))][b] = car.localTime

                    mymin = 0
                    minTime = 0
                    for n in range(len(cardict.keys())):
                        mymin = min(carTime[n])
                        if minTime == 0:
                            minTime = mymin
                        elif minTime > mymin:
                            minTime = mymin

                elif car.full == False and car.unloading and car.zeroV == False and max(car.Xpos)<finishTime:  # едет на новую погрузку
                    #запрещаем ехать на новую погрузку если по времени смена кончилась
                    car.Xpos.append((car.lempty / car.Vempty) * 60 + car.localTime)
                    car.Ypos.append(car.L + car.lempty)
                    car.yQ.append(car.sumQ)
                    car.L = car.Ypos[car.localCounter]
                    car.localTime = max(car.Xpos)

                    car.localCounter += 1
                    car.run = True
                    car.unloading = False
                    carTime[int(type1.replace('Type',''))][b] = car.localTime


                    mymin = 0
                    minTime = 0
                    for n in range(len(cardict.keys())):
                        mymin = min(carTime[n])
                        if minTime == 0:
                            minTime = mymin
                        elif minTime > mymin:
                            minTime = mymin

                excar = car
                b += 1
                if FlagOptimize == False:
                    try:
                        progress_update(minTime, workTime)
                    except:
                        pass

        starttime = minTime




def getplot():
    if cardict != {} and animAsk.get() == 0:
        carNumType = 0
        carNumCar = 0
        progress() # формируем окно для вывода прогресса

        countAllCar = 0
        counCurrentCar = 0


        for ck1 in cardict.values():
            countAllCar += len(ck1)
        if checkbox_value1.get() == 1 and animAsk.get() == 0: # обычная отрисовка без анимации
            for n in cardict.keys():

                for car in cardict[n]:

                    plt.plot(car.Xpos, car.Ypos, label = f'машина {carNumType}/{carNumCar}')
                    plt.title("Эпюра Время-расстояние")
                    plt.xlabel("Время, мин")
                    plt.ylabel("Расстояние, км")
                    plt.legend()

                    carNumCar += 1
                    counCurrentCar +=1
                    progress_update(counCurrentCar, countAllCar) # показывает прогресс по построению графика



                carNumType += 1
                carNumCar = 0

            plt.show()

        if checkbox_value1.get() == 0 and animAsk.get() == 0: # обычная отрисовка без анимации
            for n in cardict.keys():

                for car in cardict[n]:

                    plt.plot(car.Xpos, car.yQ, label = f'машина {carNumType}/{carNumCar}')
                    plt.title("Эпюра время-груз")
                    plt.xlabel("Время, мин")
                    plt.ylabel("Груз, т")
                    plt.legend()
                    carNumCar += 1
                    counCurrentCar += 1

                    progress_update(counCurrentCar, countAllCar)



                carNumType += 1
                carNumCar = 0

            plt.show()
    elif animAsk.get() == 0:
        messagebox.showerror('Нет графика', 'График не может быть построен без создания ТС')


    def sliding_frame(frame):
        y = 500 - 0.5 * frame
        if y >=10:
            return y
        else:
            return 10


    if cardict != {} and animAsk.get() == 1: # анимированная отрисовка
        carNumType = 0
        carNumCar = 0

        counCurrentCar = 0

        PlotsMas = []
        Xmas = []
        Ymas = []
        Plots_counter = 0
        Markers = [] # маркеры для графиков
        if checkbox_value1.get() == 1 and animAsk.get() == 1:
            fig, ax = plt.subplots() # отдельно плоскость и графики на ней
            for n in cardict.keys():
                for car in cardict[n]:

                    pp, = ax.plot(car.Xpos, car.Ypos)
                    mm, = ax.plot([], [], 'g^',  label = f'машина {carNumType}/{carNumCar}')
                    PlotsMas.append(pp) # запись переменных графиков
                    Markers.append(mm)
                    Markers[Plots_counter].set_color(PlotsMas[Plots_counter].get_color()) # цвет маркера соответствует цвету графика
                    Xmas.append(car.Xpos)
                    Ymas.append(car.Ypos)

                    Plots_counter += 1
                    carNumCar += 1
                    counCurrentCar += 1

                carNumType += 1
                carNumCar = 0

            plt.title("Эпюра Время-расстояние")
            plt.xlabel("Время, мин")
            plt.ylabel("Расстояние, км")
            plt.legend()

            def update(frame):
                # Обновление данных маркера в соответствии с приростом графика
                for numIter in range(Plots_counter):
                    Markers[numIter].set_data(Xmas[numIter][frame], Ymas[numIter][frame])
                    PlotsMas[numIter].set_data(Xmas[numIter][:frame + 1], Ymas[numIter][:frame + 1])

            animation = FuncAnimation(fig, update, frames=max(map(len, Ymas)), interval=sliding_frame(max(map(len, Ymas))), blit=False)


            # сохранить gif
            SafeGIF = messagebox.askyesno('Safe gif', 'Сохранить анимацию в формате .gif?')
            if SafeGIF == True:
                gifFile = filedialog.asksaveasfilename() # имя файла
                try:
                    animation.save(gifFile +".gif", writer='pillow')
                except:
                    messagebox.showinfo('Safe gif', "Gif не сохранен")

            plt.show()

        if checkbox_value1.get() == 0 and animAsk.get() == 1:
            fig, ax = plt.subplots() # отдельно плоскость и графики на ней
            for n in cardict.keys():
                for car in cardict[n]:

                    pp, = ax.plot(car.Xpos, car.yQ)
                    mm, = ax.plot([], [], 'g^',  label = f'машина {carNumType}/{carNumCar}')
                    PlotsMas.append(pp) # запись переменных графиков
                    Markers.append(mm)
                    Markers[Plots_counter].set_color(PlotsMas[Plots_counter].get_color()) # цвет маркера соответствует цвету графика
                    Xmas.append(car.Xpos)
                    Ymas.append(car.yQ)


                    plt.title("Эпюра время-груз")
                    plt.xlabel("Время, мин")
                    plt.ylabel("Груз, т")
                    plt.legend()

                    Plots_counter += 1
                    carNumCar += 1
                    counCurrentCar += 1

                carNumType += 1
                carNumCar = 0

            plt.title("Эпюра время-груз")
            plt.xlabel("Время, мин")
            plt.ylabel("Груз, т")
            plt.legend()

            def update(frame):

                for numIter in range(Plots_counter):
                    Markers[numIter].set_data(Xmas[numIter][frame], Ymas[numIter][frame])
                    PlotsMas[numIter].set_data(Xmas[numIter][:frame + 1], Ymas[numIter][:frame + 1])

            animation = FuncAnimation(fig, update, frames=max(map(len, Ymas)), interval=sliding_frame(max(map(len, Ymas))), blit=False)


            # сохранить gif
            SafeGIF = messagebox.askyesno('Safe gif', 'Сохранить анимацию в формате .gif?')
            if SafeGIF == True:
                gifFile = filedialog.asksaveasfilename() # имя файла
                try:
                    animation.save(gifFile +".gif", writer='pillow')
                except:
                    messagebox.showinfo('Safe gif', "Gif не сохранен")

            plt.show()










def Open_Condition():
    global cardict
    path = filedialog.askopenfilename()
    global starttime
    global finishTime
    global carTime
    global minTime
    global localTime
    global diggerWorkingTime
    global workTime
    global currentCircle
    global minCircle
    global carkey
    global io
    global currentType
    global delaylist
    global CarDelaySum
    global CarQSum

    global Explanation_best_genotype  # переменная для хранения лучших генотипов поколения
    global Explanation_best_score  # список для хранения лучшего значения целевой функции в поколении

    with open(path, 'r') as file_conditions:

        masterDict = json.load(file_conditions)



        def Get_data_cardict(masterDict):


            cardict = {}
            for i in masterDict['cardict'].keys():
                cardict[i] = []
                ccc = 0
                for n in masterDict['cardict'][i]:
                    cardict[i].append(cargo_car())
                    car = cardict[i][ccc]
                    ccc += 1
                    car.Vfull = masterDict['cardict'][i][n]['Vfull']
                    car.Vempty = masterDict['cardict'][i][n]['Vempty']
                    car.q = masterDict['cardict'][i][n]['q']
                    car.lempty = masterDict['cardict'][i][n]['lempty']
                    car.lfull = masterDict['cardict'][i][n]['lfull']
                    car.tloadind1 = masterDict['cardict'][i][n]['tloadind1']
                    car.tloadind2 = masterDict['cardict'][i][n]['tloadind2']
                    car.tloadind3 = masterDict['cardict'][i][n]['tloadind3']
                    car.tloadind4 = masterDict['cardict'][i][n]['tloadind4']
                    car.delay = masterDict['cardict'][i][n]['delay']

                    car.sumQ = masterDict['cardict'][i][n]['sumQ']  # суммарное количество перевезенной породы
                    car.yQ = masterDict['cardict'][i][n]['yQ']  # список с значениями изменения перевезенной породы
                    car.kg = masterDict['cardict'][i][n]['kg'] # коэффициент грузоподъемности
                    car.SumTimeDelay = masterDict['cardict'][i][n]['SumTimeDelay']  # суммарное время задержки при простоях в ожидании погрузки
                    car.rank = masterDict['cardict'][i][n]['rank'] # приоритет движения
                    car.circle = masterDict['cardict'][i][n]['circle']  # круг прохождения в цикле
                    car.run = masterDict['cardict'][i][n]['run']  # едет ли машина
                    car.loading = masterDict['cardict'][i][n]['loading']  # на погрузке ли машина
                    car.unloading = masterDict['cardict'][i][n]['unloading'] # на рагзгрузке ли машина
                    car.full = masterDict['cardict'][i][n]['full'] # заполнен ли кузов машины
                    car.waiting = masterDict['cardict'][i][n]['waiting'] # ожидает ли машина
                    car.firstTime = masterDict['cardict'][i][n]['firstTime'] # первый выезд на линию

                    car.L = masterDict['cardict'][i][n]['L'] # Суммарный пробег на маршруте
                    car.localTime = masterDict['cardict'][i][n]['localTime'] # суммарное время на маршруте
                    car.Xpos = masterDict['cardict'][i][n]['Xpos'] # данные по времени
                    car.Ypos = masterDict['cardict'][i][n]['Ypos'] # данные по пробегу
                    car.localCounter = masterDict['cardict'][i][n]['localCounter'] # локальный счетчик
                    car.TransportWork = masterDict['cardict'][i][n]['TransportWork'] # транспортная работа в т*км


            return cardict


        cardict = Get_data_cardict(masterDict)
        CarDelaySum = masterDict['CarDelaySum']  # суммарная величина простоев маши
        CarQSum = masterDict['CarQSum']  # суммарное количество перевезенной породы

        carkey = masterDict['carkey'] # идентификатор каждого типа ТС
        io = masterDict['io']
        starttime = masterDict['starttime']  # переменная локальной временной точки по которой ровняеется цикл, т.е. минимальное время временной точки из всего списка машин. Мастер-цикл в котором используется эта переменная служит временным ограничителем длительности смены или исследумеого промежутка времени
        finishTime = masterDict['finishTime'] # переменная, отвечающая за ограничение исследуемого промежутка времени в мастер-цикле
        currentCircle = masterDict['currentCircle'] # текущий круг, который уравнивает движение первых автомобилей и тех кто простаивает в очереди (список с минимумом)
        minCircle = masterDict['minCircle']  # текущий минимальый круг на всех машинах в цикле
        currentType = masterDict['currentType']  # текущий тип автомобиля, который моделируется в цикле
        workTime = masterDict['workTime'] # запись времени исследования для потенциальной оптимизации
        carTime = masterDict['carTime']
        minTime = masterDict['minTime']

        Explanation_best_genotype = masterDict['Explanation_best_genotype']  # переменная для хранения лучших генотипов поколения
        Explanation_best_score = masterDict['Explanation_best_score'] # список для хранения лучшего значения целевой функции в поколении
        # masterDict['localTime'] = localTime # Список из времени начала и окончания погрузки. Третья переменная хранит объект грузящейся машины. Четвертая - тип ТС для carTime. Пятая - номер ТС в типе для carTime
        localTime = [0, 0, 0, 0, 0]
        localTime[:2] = masterDict['localTime'][:2]
        localTime[3:5] = masterDict['localTime'][2:4]
        localTime[4]= int(localTime[4].replace('car', ''))
        localTime[2] = cardict[localTime[3]][localTime[4]]


        diggerWorkingTime = masterDict['diggerWorkingTime']  # рабочее время экскаватора
        delaylist = masterDict['delaylist'] # список для последующей записи задержки для каждой машины

        messagebox.showinfo('Open conditions', 'Восстановлено состояние из файла')
        file_conditions.close()

def Save_Condition():
    global cardict
    if cardict =={}:
        messagebox.showerror('Save conditions',f'ТС не созданы!\nНельзя записать файл')
    else:
        path = filedialog.asksaveasfilename()
        if path == '': # если прервали диалог по выбору файла
            messagebox.showerror('Save conditions', 'Состояние не сохранено')
            return
        else:
            global starttime
            global finishTime
            global carTime
            global minTime
            global localTime
            global diggerWorkingTime
            global workTime
            global currentCircle
            global minCircle
            global carkey
            global io
            global currentType
            global delaylist
            global CarDelaySum
            global CarQSum

            global Explanation_best_genotype  # переменная для хранения лучших генотипов поколения
            global Explanation_best_score  # список для хранения лучшего значения целевой функции в поколении


            def Create_data_cardict():
                dictData = {}
                for n in cardict.keys():
                    dictData[n] = {}
                    ccc = 0
                    for car in cardict[n]:
                        Sccc = "car" + str(ccc)
                        ccc +=1
                        dictData[n][Sccc] = {}
                        dictData[n][Sccc]['Vfull'] = car.Vfull
                        dictData[n][Sccc]['Vempty'] = car.Vempty
                        dictData[n][Sccc]['q'] = car.q
                        dictData[n][Sccc]['lempty'] = car.lempty
                        dictData[n][Sccc]['lfull'] = car.lfull
                        dictData[n][Sccc]['tloadind1'] = car.tloadind1
                        dictData[n][Sccc]['tloadind2'] = car.tloadind2
                        dictData[n][Sccc]['tloadind3'] = car.tloadind3
                        dictData[n][Sccc]['tloadind4'] = car.tloadind4
                        dictData[n][Sccc]['delay'] = car.delay

                        dictData[n][Sccc]['sumQ'] = car.sumQ   # суммарное количество перевезенной породы
                        dictData[n][Sccc]['yQ'] = car.yQ   # список с значениями изменения перевезенной породы
                        dictData[n][Sccc]['kg'] = car.kg   # коэффициент грузоподъемности
                        dictData[n][Sccc]['SumTimeDelay'] = car.SumTimeDelay   # суммарное время задержки при простоях в ожидании погрузки
                        dictData[n][Sccc]['rank'] = car.rank   # приоритет движения
                        dictData[n][Sccc]['circle'] = car.circle   # круг прохождения в цикле
                        dictData[n][Sccc]['run'] = car.run   # едет ли машина
                        dictData[n][Sccc]['loading'] = car.loading   # на погрузке ли машина
                        dictData[n][Sccc]['unloading'] = car.unloading   # на рагзгрузке ли машина
                        dictData[n][Sccc]['full'] = car.full   # заполнен ли кузов машины
                        dictData[n][Sccc]['waiting'] = car.waiting   # ожидает ли машина
                        dictData[n][Sccc]['firstTime'] = car.firstTime   # первый выезд на линию
                        # логические знаения говорят о том какое действие происходило перед текущим
                        dictData[n][Sccc]['L'] = car.L   # Суммарный пробег на маршруте
                        dictData[n][Sccc]['localTime'] = car.localTime   # суммарное время на маршруте
                        dictData[n][Sccc]['Xpos'] = car.Xpos  # данные по времени
                        dictData[n][Sccc]['Ypos'] = car.Ypos  # данные по пробегу
                        dictData[n][Sccc]['localCounter'] = car.localCounter   # локальный счетчик
                        dictData[n][Sccc]['TransportWork'] = car.TransportWork  # транспортная работа в т*км
                return dictData




            with open(path + '.json', 'w') as file_conditions:
                masterDict = {}
                masterDict['CarDelaySum'] = CarDelaySum # суммарная величина простоев маши
                masterDict['CarQSum'] = CarQSum  # суммарное количество перевезенной породы
                masterDict['cardict'] = Create_data_cardict()  # словарь для записи эксемпляров класса cargo_car по указанному виду ТС
                masterDict['carkey'] = carkey  # идентификатор каждого типа ТС
                masterDict['io'] = io
                masterDict['workTime'] = workTime # запись рабочего времени (важно для последующей оптимизации)
                masterDict['starttime'] = starttime # переменная локальной временной точки по которой ровняеется цикл, т.е. минимальное время временной точки из всего списка машин. Мастер-цикл в котором используется эта переменная служит временным ограничителем длительности смены или исследумеого промежутка времени
                masterDict['finishTime'] = finishTime # переменная, отвечающая за ограничение исследуемого промежутка времени в мастер-цикле
                masterDict['currentCircle'] = currentCircle  # текущий круг, который уравнивает движение первых автомобилей и тех кто простаивает в очереди (список с минимумом)
                masterDict['minCircle'] = minCircle # текущий минимальый круг на всех машинах в цикле
                masterDict['currentType'] = currentType  # текущий тип автомобиля, который моделируется в цикле
                masterDict['carTime'] = carTime
                masterDict['minTime'] = minTime
                masterDict['Explanation_best_genotype']= Explanation_best_genotype
                masterDict['Explanation_best_score']= Explanation_best_score
                #masterDict['localTime'] = localTime # Список из времени начала и окончания погрузки. Третья переменная хранит объект грузящейся машины. Четвертая - тип ТС для carTime. Пятая - номер ТС в типе для carTime
                localTimeListData = [] # список данных из localTime для json
                localTimeListData.append(localTime[0])
                localTimeListData.append(localTime[1])
                localTimeListData.append('Type' + str(localTime[3]))
                localTimeListData.append('car' + str(localTime[4]))


                masterDict['localTime'] = localTimeListData

                masterDict['diggerWorkingTime'] = diggerWorkingTime # рабочее время экскаватора
                masterDict['delaylist'] = delaylist  # список для последующей записи задержки для каждой машины
                json.dump(masterDict, file_conditions)
                messagebox.showinfo('Save conditions', 'Состояние сохранено')
                file_conditions.close()





def delAll():
    delq = messagebox.askyesno('Удаление данных', f'Данные будут безвозвратно удалены!\n Хотите продолжить?')
    if delq == True:
        #полное обнуление
        global starttime
        global finishTime
        global cardict
        global carTime
        global minTime
        global localTime
        global diggerWorkingTime
        global workTime
        global currentCircle
        global minCircle
        global carkey
        global io
        global currentType
        global delaylist
        global CarDelaySum
        global CarQSum

        global Explanation_best_genotype  # переменная для хранения лучших генотипов поколения
        global Explanation_best_score  # список для хранения лучшего значения целевой функции в поколении

        Explanation_best_genotype = []
        Explanation_best_score = []

        CarDelaySum = 0  # суммарная величина простоев машин
        CarQSum = 0  # суммарное количество перевезенной породы

        cardict = {}  # словарь для записи эксемпляров класса cargo_car по указанному виду ТС
        carkey = 0  # идентификатор каждого типа ТС
        io = 0
        starttime = 0  # переменная локальной временной точки по которой ровняеется цикл, т.е. минимальное время временной точки из всего списка машин. Мастер-цикл в котором используется эта переменная служит временным ограничителем длительности смены или исследумеого промежутка времени
        finishTime = 0  # переменная, отвечающая за ограничение исследуемого промежутка времени в мастер-цикле
        currentCircle = []  # текущий круг, который уравнивает движение первых автомобилей и тех кто простаивает в очереди (список с минимумом)
        minCircle = 0  # текущий минимальый круг на всех машинах в цикле
        currentType = 0  # текущий тип автомобиля, который моделируется в цикле
        carTime = []
        minTime = 0
        localTime = [0, 0, 0, 0,
                     0]  # Список из времени начала и окончания погрузки. Третья переменная хранит объект грузящейся машины. Четвертая - тип ТС для carTime. Пятая - номер ТС в типе для carTime
        diggerWorkingTime = 0  # рабочее время экскаватора
        delaylist = []  # список для последующей записи задержки для каждой машины

        countcar['text'] = ("Количество ТС тип" + str(carkey))  # меняем этикетку

        #Очищаем все окна ввода
        delayE.delete(0, END)

        VfullE.delete(0, END)
        VemptyE.delete(0, END)
        qE.delete(0, END)
        lemptyE.delete(0, END)
        lfullE.delete(0, END)
        tloadind1E.delete(0, END)
        tloadind2E.delete(0, END)
        tloadind3E.delete(0, END)
        tloadind4E.delete(0, END)
        countcarE.delete(0, END)

        kgE.delete(0, END)
        rankE.delete(0, END)
        messagebox.showinfo('Removal','Все данные успешно стерты')


        workTime = simpledialog.askfloat('Work time', 'Укажите рабочее время в минутах', parent=window)
        workTimeaskagain()



# Процедуа перезаписи и поверки параметра рабочего времени
def workTimeaskagain():
    global workTime

    if workTime == None:
        messagebox.showerror('Error', f'Рабочее время должно быть задано!\nУкажите значение параметра снова')
        workTime = simpledialog.askfloat('Work time', 'Укажите рабочее время в минутах', parent=window)
        workTimeaskagain()
    elif workTime < 0:
        messagebox.showerror('Error', f'Рабочее время не может быть отрицательным!\nУкажите значение параметра снова')
        workTime = simpledialog.askfloat('Work time', 'Укажите рабочее время в минутах', parent=window)
        workTimeaskagain()




def progress():
    global progress_window, progressbar

    progress_window = tk.Toplevel()

    progress_window.title('progress')
    progressbar = ttk.Progressbar(progress_window, orient="horizontal", length=300, mode="determinate")

    progressbar.pack(pady=10)
    screen_width = progress_window.winfo_screenwidth() # определяем ширину экрана
    screen_height = progress_window.winfo_screenheight()
    x = (screen_width - progressbar.winfo_reqwidth()) // 2 # вычисляем координаты для центрирования окна
    y = (screen_height - progressbar.winfo_reqheight()) // 2
    progress_window.geometry('{}x{}+{}+{}'.format(progressbar.winfo_reqwidth(), progressbar.winfo_reqheight()+20,
                                                  x, y)) # центрируем по экрану

def progress_update(timec, timeAll):
    global progress_window, progressbar
    try:
        progressbar["value"] = timec / timeAll*100
        progress_window.update()  # обновляем окно
        progressbar.update()  # обновляем прогрессбар
    except:
        progress_window.destroy()  # закрываем окно


    if timec >= timeAll:
        progress_window.destroy()  # закрываем окно







window = Tk() # создаем окно приложени
#window.iconbitmap(r"mainccar.ico")
#window.geometry('500x435')
window.title('Mining problem')




frame = Frame(
   window,
   padx = 40,
   pady = 10
)
frame.pack(expand=True)

frame2  = Frame(window, padx = 10, #Задаём отступ по горизонтали
   pady = 10 #Задаём отступ по вертикали. Так как frame2 после frame, то отступ по вертикаль отключен
                )
frame2.pack(expand = True)





checkbox_value1 = tk.BooleanVar()
checkbox_value1.set(1)
radbtn1 = Radiobutton(frame2, text = 'Эпюра время-расстояние', variable =checkbox_value1, value = 1)
radbtn2 = Radiobutton(frame2, text = 'Эпюра время-груз', variable =checkbox_value1, value = 0)

radbtn1.grid(row = 1, column =1, sticky ='w')
radbtn2.grid(row = 1, column =2, sticky ='w')
btnPlot = Button(frame2, text ='Показать график', command = getplot)
btnPlot.grid(row = 1, column =3)


animAsk = tk.BooleanVar()
animbut = Checkbutton(frame2, text = 'Анимировать график', variable = animAsk)
animbut.grid(row = 3, column =2)


authorname = Label(
   frame,
   text="by Matveev A.G."
)
authorname.grid(row=2, column=2)

import webbrowser
def urlgo(event):
    messagebox.showinfo('Author contacts','Электронная почта: alexzandermatveev@yandex.ru\nTelegram: @alexzmat')

authorname.bind("<Button-1>", urlgo)

Vfull = Label(
   frame,
   text="Cкорость при полном кузове, км/ч"

)
Vfull.grid(row=3, column=1, sticky="w")
VfullE = Entry(
   frame,
)
VfullE.grid(row=3, column=2)

Vempty = Label(
   frame,
   text="Cкорость при пустом кузове, км/ч"

)
Vempty.grid(row=4, column=1, sticky="w")
VemptyE = Entry(
   frame,
)
VemptyE.grid(row=4, column=2)

q = Label(
   frame,
   text="Грузоподъемность, т"

)
q.grid(row=5, column=1, sticky="w")
qE = Entry(
   frame,
)
qE.grid(row=5, column=2)

lempty = Label(
   frame,
   text="Порожняя часть ездки, км",

)
lempty.grid(row=6, column=1, sticky="w")
lemptyE = Entry(
   frame,
)
lemptyE.grid(row=6, column=2)

lfull = Label(
   frame,
   text="Груженная часть ездки, км"

)
lfull.grid(row=7, column=1, sticky="w")
lfullE = Entry(
   frame,
)
lfullE.grid(row=7, column=2)

tloadind1 = Label(
   frame,
   text="Время затрачиваемое под установку на погрузку, мин",

)
tloadind1.grid(row=8, column=1, sticky="w")
tloadind1E = Entry(
   frame,
)
tloadind1E.grid(row=8, column=2)

tloadind2 = Label(
   frame,
   text="Время погрузки, мин"

)
tloadind2.grid(row=9, column=1, sticky="w")
tloadind2E = Entry(
   frame,
)
tloadind2E.grid(row=9, column=2)

tloadind3 = Label(
   frame,
   text="Время, затрачиваемое установку под разгрузку, мин",

)
tloadind3.grid(row=10, column=1, sticky="w") # sticky="w" - выравнивает элемент в grid по левой стороне
tloadind3E = Entry(
   frame,
)
tloadind3E.grid(row=10, column=2)

tloadind4 = Label(
   frame,
   text="Время разгрузки, мин",

)
tloadind4.grid(row=11, column=1, sticky="w")
tloadind4E = Entry(
   frame,
)
tloadind4E.grid(row=11, column=2)


kg = Label(
   frame,
   text="Коэффициент грузоподъемности"

)
kg.grid(row=12, column=1, sticky="w")
kgE = Entry(
   frame,
)
kgE.grid(row=12, column=2)


countcar = Label(
   frame,
   text="Количество ТС тип0"

)
countcar.grid(row=13, column=1, sticky="w")
countcarE = Entry(
   frame,
)
countcarE.grid(row=13, column=2)


delay = Label(
   frame,
   text="Задержка выпуска на линию, мин"

)
delay.grid(row=14, column=1,   sticky="w")
delayE = Entry(
   frame,
)
delayE.grid(row=14,  column=2)



rank = Label(
   frame,
   text="Приоритет движения" # по убыванию, Где 1 - самый низший ранг

)
rank.grid(row=15, column=1, sticky="w")
rankE = Entry(
   frame,
)
rankE.grid(row=15, column=2)

btn1 = Button(
   frame,
   text='Моделировать',
    command = mes2
)
btn1.grid(row=17, column=2)


saveConBut = Button(
   frame,
   text='Сохранить состояние',
    command = Save_Condition
)
saveConBut.grid(row=18, column=1)

openConBut = Button(
   frame,
   text='Восстановить состояние',
    command = Open_Condition
)
openConBut.grid(row=18, column=2)



btn2 = Button(
   frame,
   text='Создать ТС',
    command = mes
)
btn2.grid(row=17, column=1)

btnDel = Button(
   frame2,
   text='Стереть',
    command = delAll
)
btnDel.grid(row=2, column=1)

btnCSV = Button(
   frame2,
   text='Записать данные',
    command = saveCSV
)
btnCSV.grid(row=2, column=2)

Optbut = Button(
   frame2,
   text='Оптимизировать',
    command = OptimizeBut
)
Optbut.grid(row=2, column=3)

SumInfo = Button(
   frame2,
   text='Сводная информация',
    command = ShowSuminfo
)
SumInfo.grid(row=3, column=1)

workTime = simpledialog.askfloat('Work time','Укажите рабочее время в минутах', parent = window)
window.deiconify() # восстановить окно с интерефейсом
workTimeaskagain()



window.mainloop()
