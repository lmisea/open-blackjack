public class PruebaOvalosRectangulosLineas {
    
    public static void main(String[] args) {
	MaquinaDeTrazados mt = new MaquinaDeTrazados(400, 250, "Prueba de figuras", Colores.LIGHT_GRAY);
	mt.dibujarLinea(5, 15, 380, 15);
	mt.dibujarLinea(5, 30, 380, 30, Colores.RED);
	mt.dibujarRectangulo(5, 40, 90, 55, Colores.BLUE);
	mt.dibujarRectanguloLleno(100, 40, 90, 55, Colores.YELLOW);
	mt.dibujarOvaloLleno(195, 40, 90, 55, Colores.CYAN);
	mt.dibujarOvalo(290, 40, 90, 55, Colores.GREEN);
	mt.dibujarRectanguloLleno(5, 100, 90, 55);
	mt.dibujarRectangulo(100, 100, 90, 55);
	mt.dibujarOvalo(195, 100, 90, 55);
	mt.dibujarOvaloLleno(290, 100, 90, 55);
	mt.mostrar();
    }
}
