# Primera entrega del proyecto final
## Integrantes: Isea, Luis (19-10175) y Prieto, Jesús (19-10211)

El proyecto final del **Laboratorio de Algoritmos y Estructuras I (CI-2691)** consiste en un juego de *BlackJack* implementado en *OpenJML*. Esta es la primera entrega de dicho proyecto.

## Compilar y ejecutar la aplicación

Para compilar:

```
openjml --rac -cp maquina_trazados/lib/maquinaTrazados-v0.1.jar Blackjack.java
```

Para hacer la verificación estática:

```
openjml --esc --exclude main -cp maquina_trazados/lib/maquinaTrazados-v0.1.jar Blackjack.java
```

Para ejecutar el programa:

```
openjml-java -cp maquina_trazados/lib/maquinaTrazados-v0.1.jar:. Blackjack.java
```
