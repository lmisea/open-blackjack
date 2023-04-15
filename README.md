# Segunda y última entrega del proyecto final
### Integrantes: Isea, Luis (19-10175) y Prieto, Jesús (19-10211)

El proyecto final del **Laboratorio de Algoritmos y Estructuras I (CI-2691)** consiste en un juego de *BlackJack* implementado en *OpenJML*. Esta es la segunda y última entrega de dicho proyecto.

El juego cuenta con un sistema de apuestas simple basado en créditos, que el usuario puede ganar o perder dependiendo si es capaz o no de llegar más cerca a 21 que el *crupier* (quien es interpretado por la computadora), sin llegar a pasarse de 21.

## Compilar y ejecutar la aplicación

Para compilar:

```
openjml --rac -cp maquina_trazados/lib/maquinaTrazados-v0.1.jar Blackjack.java
```

Para hacer la verificación estática (tarda bastante, por lo que se pide paciencia):

```
openjml --esc --exclude main,consultarDecisionJugador,dibujarMesaBlackjack,dibujarCartasCrupier,dibujarCartasJugador,determinarSiSeJugaraOtraMano,determinarResultadoMano,doblarApuesta,mensajeBienvenida,obtenerApuesta,mostrarPuntuacionesPorTexto,mostrarCreditosPorTexto -cp maquina_trazados/lib/maquinaTrazados-v0.1.jar Blackjack.java
```

Para ejecutar el programa:

```
openjml-java -cp maquina_trazados/lib/maquinaTrazados-v0.1.jar:. Blackjack.java
```
