# The_mine

## Введение
Исходная идея проекта возникла в рамках работы, направленной на решение проблемы организации работы автомобилей-самосвалов и экскаваторов в циклических маятниковых перевозках на угольном разрезе. Различные модели автомобилей в колонне обладали уникальными характеристиками, препятствующих эффективному выполнению совместной работы. Для улучшения ситуации были разработаны правила проезда на точках погрузки, которые устанавливали порядок погрузки в зависимости от модели транспортного средства.

## Производственная проблема
Мы рассматриваем проблему на примере реальной производственной задачи, возникшей на угольном разрезе предприятия АО «Черниговец». На данном месторождении добыча ведется открытым способом, и для реализации внутренней логистики задействуются автомобильно-экскаваторные комплексы, включающие в себя экскаваторы P&H-2800 и карьерные самосвалы БелАЗ-75306 (грузоподъемность 240 тонн). В качестве эксперимента в состав одного комплекса был добавлен БелАЗ-75710 (грузоподъемность 450 тонн), значительно отличающийся по своим характеристикам от других моделей самосвалов. Работа этих самосвалов и экскаваторов по вывозу породы из карьера осуществляется через [два заезда под погрузку экскаватора](digpic.png) несколькими сменами (каждая по 11 часов). Порядок загрузки происходит по очереди на каждом пункте погрузки.

![Схема работы экскаватора на 2 подъезда](digpic.png)*Схема работы экскаватора на 2 подъезда*

Описанный выше базовый план работы одного участка погрузки на предприятии приводил к простою одного экскаватора в течение 173 минут, а суммарные простои 7 БелАЗов из 11-часовой смены составляли 474,3 минуты. Это, в свою очередь, приводило к значительным финансовым убыткам для предприятия.

## Что делает проект
Представленная программа помогает строить модели совместной работы нескольких транспортных средств (ТС) с возможностью детального представления свойств агента на каждой интеграции в течении всего времени исследования.
### Знакомство с программой
Сначала программа запрашивает «Рабочее время» в минутах (рис. 1). Это значение представляет собой временной отрезок, в течение которого будет производиться моделирование и исследование процессов.

![Рис. 1. Указание параметра "рабочего времени" в минутах](pic1.png)*Рис. 1. Указание параметра "рабочего времени" в минутах*



## Как начать работу
1.	загрузите файл .py из репозитория;
2.	установите необходимые библиотеки, включая scikit-learn и matplotlib;
3.	запустите файл .py.
Используйте интуитивно понятный GUI и следуйте дополнительным сообщениям для первоначальной настройки. Ознакомьтесь с инструкцией [ссылке](https://disk.yandex.ru/i/g4RggZGAa_s_ig) для более глубокого понимания функционала.

## Полезность проекта
Проект полезен для моделирования взаимосвязей в работе и последующих корректировок и улучшений. Пользователи могут анализировать различные модели и оптимизировать маршруты для повышения эффективности процессов. Несмотря на кажущуюся простоту и отношение к проблеме горнодобывающей отрасли, сценариев применения данной программы достаточно много. Так, например, можно моделировать, исследовать и оптимизировать движение городского транспорта, добиваясь устойчивого промежутка времени между ТС, их скорости или конкретного времени прибытия на остановку или конечный пункт; можно попробовать алгоритм под логистику складского хозяйства, рассматривая в виде агентов отдельные товары, работников или места хранения; можно попробовать использовать программу в управлении людьми или проектами и многое другое. Вместе с тем, добавленная возможность интерпретации эвристических решений позволит пользователю углубить свое понимание и исследуемом вопросе и поможет указать направления улучшения решаемой задачи.
